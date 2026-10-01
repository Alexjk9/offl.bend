import { readFileSync, writeFileSync } from "node:fs";
import { dirname, basename, extname, join, resolve, relative } from "node:path";

const MAGIC = 0x46546c67;
const JSON_CHUNK = 0x4e4f534a;
const BIN_CHUNK = 0x004e4942;
const FORMAT_MAGIC = 0x48534d42;
const FORMAT_VERSION = 5;
const NONE = 0xffffffff;
const NAME_WORDS = 8;
const SIZES = { SCALAR: 1, VEC2: 2, VEC3: 3, VEC4: 4, MAT2: 4, MAT3: 9, MAT4: 16 };
const BYTES = { 5120: 1, 5121: 1, 5122: 2, 5123: 2, 5125: 4, 5126: 4 };
const NORMS = { 5120: 127, 5121: 255, 5122: 32767, 5123: 65535 };
const MIME = { "image/png": ".png", "image/jpeg": ".jpg", "image/webp": ".webp" };
const FLAG_BASE = 1;
const FLAG_MR = 2;
const FLAG_NORMAL = 4;
const IDENTITY = [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1];

function fail(message) {
  console.error("glb2mesh: " + message);
  process.exit(1);
}

function warn(message) {
  console.error("glb2mesh: warning: " + message);
}

function dataUri(uri) {
  const m = /^data:([^;,]*)(;base64)?,(.*)$/s.exec(uri);
  if (!m) return null;
  return { mime: m[1], bytes: m[2] ? Buffer.from(m[3], "base64") : Buffer.from(decodeURIComponent(m[3]), "latin1") };
}

function open(path) {
  const bytes = readFileSync(path);
  const dir = dirname(path);
  let doc, bin = null;
  if (bytes.length >= 12 && bytes.readUInt32LE(0) === MAGIC) {
    if (bytes.readUInt32LE(4) !== 2) fail("GLB version " + bytes.readUInt32LE(4) + " is not supported");
    for (let at = 12; at + 8 <= bytes.length;) {
      const size = bytes.readUInt32LE(at);
      const type = bytes.readUInt32LE(at + 4);
      const data = bytes.subarray(at + 8, at + 8 + size);
      if (type === JSON_CHUNK) doc = JSON.parse(data.toString("utf8"));
      else if (type === BIN_CHUNK) bin = data;
      at += 8 + size;
    }
    if (!doc) fail("GLB has no JSON chunk");
  } else {
    doc = JSON.parse(bytes.toString("utf8"));
  }
  if (!doc.asset || !/^2\./.test(doc.asset.version)) fail("glTF version " + (doc.asset && doc.asset.version) + " is not supported");
  const KNOWN = new Set(["KHR_materials_emissive_strength", "EXT_texture_webp", "KHR_mesh_quantization"]);
  for (const ext of doc.extensionsRequired ?? []) if (!KNOWN.has(ext)) fail("required extension " + ext + " is not supported");
  for (const ext of doc.extensionsUsed ?? []) if (!KNOWN.has(ext)) warn("extension " + ext + " is ignored");
  doc.bin = (doc.buffers ?? []).map((b, i) => {
    if (b.uri === undefined) {
      if (i !== 0 || !bin) fail("buffer " + i + " has no uri and no BIN chunk");
      return bin;
    }
    const inline = dataUri(b.uri);
    return inline ? inline.bytes : readFileSync(join(dir, decodeURIComponent(b.uri)));
  });
  doc.dir = dir;
  doc.parents = new Map();
  (doc.nodes ?? []).forEach((node, i) => { for (const c of node.children ?? []) doc.parents.set(c, i); });
  return doc;
}

function component(view, at, type) {
  switch (type) {
    case 5120: return view.getInt8(at);
    case 5121: return view.getUint8(at);
    case 5122: return view.getInt16(at, true);
    case 5123: return view.getUint16(at, true);
    case 5125: return view.getUint32(at, true);
    case 5126: return view.getFloat32(at, true);
    default: fail("component type " + type + " is not supported");
  }
}

function viewOf(doc, index) {
  const v = doc.bufferViews[index];
  const buf = doc.bin[v.buffer];
  const off = v.byteOffset ?? 0;
  return { view: new DataView(buf.buffer, buf.byteOffset + off, v.byteLength), stride: v.byteStride };
}

function accessor(doc, index) {
  const a = doc.accessors[index];
  const n = SIZES[a.type];
  const bytes = BYTES[a.componentType];
  if (n === undefined || bytes === undefined) fail("accessor " + index + " has an unsupported type");
  const out = new Float64Array(a.count * n);
  if (a.bufferView !== undefined) {
    const { view, stride = n * bytes } = viewOf(doc, a.bufferView);
    const base = a.byteOffset ?? 0;
    for (let k = 0; k < a.count; k += 1) {
      for (let j = 0; j < n; j += 1) {
        out[k * n + j] = component(view, base + k * stride + j * bytes, a.componentType);
      }
    }
  }
  if (a.sparse) {
    const s = a.sparse;
    const ids = viewOf(doc, s.indices.bufferView).view;
    const vals = viewOf(doc, s.values.bufferView).view;
    const idBytes = BYTES[s.indices.componentType];
    for (let k = 0; k < s.count; k += 1) {
      const target = component(ids, (s.indices.byteOffset ?? 0) + k * idBytes, s.indices.componentType);
      for (let j = 0; j < n; j += 1) {
        out[target * n + j] = component(vals, (s.values.byteOffset ?? 0) + (k * n + j) * bytes, a.componentType);
      }
    }
  }
  if (a.normalized && NORMS[a.componentType]) {
    const m = NORMS[a.componentType];
    for (let i = 0; i < out.length; i += 1) out[i] = Math.max(out[i] / m, -1);
  }
  return { data: out, n, count: a.count };
}

function mat4Mul(a, b) {
  const out = new Array(16).fill(0);
  for (let c = 0; c < 4; c += 1) {
    for (let r = 0; r < 4; r += 1) {
      let s = 0;
      for (let k = 0; k < 4; k += 1) s += a[k * 4 + r] * b[c * 4 + k];
      out[c * 4 + r] = s;
    }
  }
  return out;
}

function trsMatrix(t, q, s) {
  const [tx, ty, tz] = t;
  const [qx, qy, qz, qw] = q;
  const [sx, sy, sz] = s;
  const xx = qx * qx, yy = qy * qy, zz = qz * qz, xy = qx * qy, xz = qx * qz, yz = qy * qz;
  const wx = qw * qx, wy = qw * qy, wz = qw * qz;
  return [
    (1 - 2 * (yy + zz)) * sx, 2 * (xy + wz) * sx, 2 * (xz - wy) * sx, 0,
    2 * (xy - wz) * sy, (1 - 2 * (xx + zz)) * sy, 2 * (yz + wx) * sy, 0,
    2 * (xz + wy) * sz, 2 * (yz - wx) * sz, (1 - 2 * (xx + yy)) * sz, 0,
    tx, ty, tz, 1,
  ];
}

function decompose(m) {
  const col = (c) => [m[c * 4], m[c * 4 + 1], m[c * 4 + 2]];
  const len = (v) => Math.hypot(v[0], v[1], v[2]);
  const [c0, c1, c2] = [col(0), col(1), col(2)];
  const det = c0[0] * (c1[1] * c2[2] - c1[2] * c2[1]) - c1[0] * (c0[1] * c2[2] - c0[2] * c2[1]) + c2[0] * (c0[1] * c1[2] - c0[2] * c1[1]);
  const s = [len(c0) * (det < 0 ? -1 : 1), len(c1), len(c2)];
  const r = [c0.map((v) => v / s[0]), c1.map((v) => v / s[1]), c2.map((v) => v / s[2])];
  const [[r00, r10, r20], [r01, r11, r21], [r02, r12, r22]] = r;
  const trace = r00 + r11 + r22;
  let q;
  if (trace > 0) {
    const k = Math.sqrt(trace + 1) * 2;
    q = [(r21 - r12) / k, (r02 - r20) / k, (r10 - r01) / k, k / 4];
  } else if (r00 > r11 && r00 > r22) {
    const k = Math.sqrt(1 + r00 - r11 - r22) * 2;
    q = [k / 4, (r01 + r10) / k, (r02 + r20) / k, (r21 - r12) / k];
  } else if (r11 > r22) {
    const k = Math.sqrt(1 + r11 - r00 - r22) * 2;
    q = [(r01 + r10) / k, k / 4, (r12 + r21) / k, (r02 - r20) / k];
  } else {
    const k = Math.sqrt(1 + r22 - r00 - r11) * 2;
    q = [(r02 + r20) / k, (r12 + r21) / k, k / 4, (r10 - r01) / k];
  }
  return { t: [m[12], m[13], m[14]], r: unitQuat(q), s };
}

function trs(node) {
  if (node.matrix) return decompose(node.matrix);
  return { t: node.translation ?? [0, 0, 0], r: node.rotation ?? [0, 0, 0, 1], s: node.scale ?? [1, 1, 1] };
}

function nodeMatrix(node) {
  if (node.matrix) return node.matrix.slice();
  const { t, r, s } = trs(node);
  return trsMatrix(t, r, s);
}

function normalMatrix(m) {
  const [a, b, c, , d, e, f, , g, h, i] = m;
  const det = a * (e * i - f * h) - d * (b * i - c * h) + g * (b * f - c * e);
  const id = det === 0 ? 0 : 1 / det;
  const inv = [
    (e * i - f * h) * id, (c * h - b * i) * id, (b * f - c * e) * id,
    (f * g - d * i) * id, (a * i - c * g) * id, (c * d - a * f) * id,
    (d * h - e * g) * id, (b * g - a * h) * id, (a * e - b * d) * id,
  ];
  return [inv[0], inv[3], inv[6], inv[1], inv[4], inv[7], inv[2], inv[5], inv[8]];
}

function point(m, x, y, z) {
  return [
    m[0] * x + m[4] * y + m[8] * z + m[12],
    m[1] * x + m[5] * y + m[9] * z + m[13],
    m[2] * x + m[6] * y + m[10] * z + m[14],
  ];
}

function direction(m, x, y, z) {
  return [m[0] * x + m[3] * y + m[6] * z, m[1] * x + m[4] * y + m[7] * z, m[2] * x + m[5] * y + m[8] * z];
}

function unit([x, y, z]) {
  const l = Math.hypot(x, y, z) || 1;
  return [x / l, y / l, z / l];
}

function unitQuat(q) {
  const l = Math.hypot(q[0], q[1], q[2], q[3]) || 1;
  return q.map((v) => v / l);
}

function slerp(a, b, t) {
  let d = a[0] * b[0] + a[1] * b[1] + a[2] * b[2] + a[3] * b[3];
  let flip = 1;
  if (d < 0) { d = -d; flip = -1; }
  if (d > 0.9995) return unitQuat(a.map((v, i) => v + (b[i] * flip - v) * t));
  const theta = Math.acos(Math.min(1, d));
  const s = Math.sin(theta);
  const wa = Math.sin((1 - t) * theta) / s;
  const wb = Math.sin(t * theta) / s * flip;
  return unitQuat(a.map((v, i) => v * wa + b[i] * wb));
}

function triangles(mode, ids) {
  const out = [];
  if (mode === 4) {
    for (let i = 0; i + 2 < ids.length; i += 3) out.push(ids[i], ids[i + 1], ids[i + 2]);
  } else if (mode === 5) {
    for (let i = 0; i + 2 < ids.length; i += 1) {
      if (i % 2 === 0) out.push(ids[i], ids[i + 1], ids[i + 2]);
      else out.push(ids[i + 1], ids[i], ids[i + 2]);
    }
  } else if (mode === 6) {
    for (let i = 1; i + 1 < ids.length; i += 1) out.push(ids[0], ids[i], ids[i + 1]);
  } else {
    return null;
  }
  return out;
}

function material(doc, index, images) {
  const m = index === undefined ? {} : doc.materials[index];
  const pbr = m.pbrMetallicRoughness ?? {};
  const base = pbr.baseColorFactor ?? [1, 1, 1, 1];
  let flags = 0;
  const use = (info, kind, flag) => {
    if (!info) return;
    if ((info.texCoord ?? 0) !== 0) warn("material " + index + " uses TEXCOORD_" + info.texCoord + " for its " + kind + " texture; only TEXCOORD_0 is read");
    const tex = doc.textures[info.index];
    const source = tex.extensions?.EXT_texture_webp?.source ?? tex.source;
    if (source === undefined) return;
    images.push({ image: source, material: index ?? 0, kind });
    flags |= flag;
  };
  use(pbr.baseColorTexture, "base", FLAG_BASE);
  use(pbr.metallicRoughnessTexture, "mr", FLAG_MR);
  use(m.normalTexture, "normal", FLAG_NORMAL);
  return {
    base, metallic: pbr.metallicFactor ?? 1, roughness: pbr.roughnessFactor ?? 1, flags,
    normalScale: m.normalTexture ? m.normalTexture.scale ?? 1 : 1,
    emissive: (m.emissiveFactor ?? [0, 0, 0]).map((v) => v * (m.extensions?.KHR_materials_emissive_strength?.emissiveStrength ?? 1)),
  };
}

function skinOf(doc, skin, index) {
  const set = new Set(skin.joints);
  const ancestors = (n) => {
    const out = [];
    for (let p = doc.parents.get(n); p !== undefined; p = doc.parents.get(p)) out.push(p);
    return out;
  };
  const order = skin.joints.map((node, orig) => ({ node, orig, depth: ancestors(node).filter((a) => set.has(a)).length }))
    .sort((a, b) => a.depth - b.depth || a.orig - b.orig);
  const remap = new Map(order.map((j, k) => [j.orig, k]));
  const byNode = new Map(order.map((j, k) => [j.node, k]));
  const binds = skin.inverseBindMatrices !== undefined ? accessor(doc, skin.inverseBindMatrices).data : null;
  const joints = order.map((j, k) => {
    let pre = IDENTITY;
    let parent = NONE;
    for (const a of ancestors(j.node)) {
      if (set.has(a)) { parent = byNode.get(a); break; }
      pre = mat4Mul(nodeMatrix(doc.nodes[a]), pre);
    }
    const node = doc.nodes[j.node];
    return {
      name: node.name ?? "joint" + k, node: j.node, parent, pre, rest: trs(node),
      bind: binds ? Array.from(binds.subarray(j.orig * 16, j.orig * 16 + 16)) : IDENTITY,
    };
  });
  if (joints.length > 256) fail("skin " + index + " has " + joints.length + " joints; at most 256 are supported");
  return { joints, remap, byNode };
}

function primitive(doc, prim, world, images, skinIndex, skin) {
  const mode = prim.mode ?? 4;
  if (prim.attributes.POSITION === undefined) fail("a primitive has no POSITION");
  const pos = accessor(doc, prim.attributes.POSITION);
  const nor = prim.attributes.NORMAL !== undefined ? accessor(doc, prim.attributes.NORMAL) : null;
  const tan = prim.attributes.TANGENT !== undefined ? accessor(doc, prim.attributes.TANGENT) : null;
  const uv = prim.attributes.TEXCOORD_0 !== undefined ? accessor(doc, prim.attributes.TEXCOORD_0) : null;
  const skinned = skin !== null && prim.attributes.JOINTS_0 !== undefined && prim.attributes.WEIGHTS_0 !== undefined;
  const jnt = skinned ? accessor(doc, prim.attributes.JOINTS_0) : null;
  const wgt = skinned ? accessor(doc, prim.attributes.WEIGHTS_0) : null;
  for (const name of Object.keys(prim.attributes)) {
    if (!["POSITION", "NORMAL", "TANGENT", "TEXCOORD_0", "JOINTS_0", "WEIGHTS_0"].includes(name)) warn("attribute " + name + " is dropped");
  }
  if (prim.targets) warn("morph targets are dropped");
  const ids = prim.indices !== undefined ? Array.from(accessor(doc, prim.indices).data)
    : Array.from({ length: pos.count }, (_, i) => i);
  const tris = triangles(mode, ids);
  if (tris === null) {
    warn("primitive mode " + mode + " is skipped");
    return null;
  }
  const xf = skinned ? IDENTITY : world;
  const nm = normalMatrix(xf);
  const lo = [Infinity, Infinity, Infinity];
  const hi = [-Infinity, -Infinity, -Infinity];
  const record = (k, flat) => {
    const p = point(xf, pos.data[k * 3], pos.data[k * 3 + 1], pos.data[k * 3 + 2]);
    for (let d = 0; d < 3; d += 1) { lo[d] = Math.min(lo[d], p[d]); hi[d] = Math.max(hi[d], p[d]); }
    const n = nor ? unit(direction(nm, nor.data[k * 3], nor.data[k * 3 + 1], nor.data[k * 3 + 2])) : flat;
    const t = tan ? [...unit(direction(nm, tan.data[k * 4], tan.data[k * 4 + 1], tan.data[k * 4 + 2])), tan.data[k * 4 + 3]] : [0, 0, 0, 0];
    const st = uv ? [uv.data[k * 2], uv.data[k * 2 + 1]] : [0, 0];
    const out = [...p, ...n, ...t, ...st];
    if (skinned) {
      const w = [0, 1, 2, 3].map((c) => Math.max(0, wgt.data[k * 4 + c]));
      const sum = w.reduce((a, b) => a + b, 0);
      const joints = [0, 1, 2, 3].map((c) => skin.remap.get(jnt.data[k * 4 + c]) ?? 0);
      out.push(joints[0] | (joints[1] << 8) | (joints[2] << 16) | (joints[3] << 24), ...(sum > 0 ? w.map((v) => v / sum) : [1, 0, 0, 0]));
    }
    return out;
  };
  const flatNormal = (a, b, c) => {
    const [pa, pb, pc] = [a, b, c].map((k) => point(xf, pos.data[k * 3], pos.data[k * 3 + 1], pos.data[k * 3 + 2]));
    const u = [pb[0] - pa[0], pb[1] - pa[1], pb[2] - pa[2]];
    const v = [pc[0] - pa[0], pc[1] - pa[1], pc[2] - pa[2]];
    return unit([u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]);
  };
  const local = new Map();
  const verts = [];
  const faces = [];
  for (let i = 0; i < tris.length; i += 3) {
    const flat = nor ? null : flatNormal(tris[i], tris[i + 1], tris[i + 2]);
    for (let j = 0; j < 3; j += 1) {
      const k = tris[i + j];
      const key = nor ? k : "f" + i + "." + j;
      if (!local.has(key)) { local.set(key, verts.length); verts.push(record(k, flat)); }
      faces.push(local.get(key));
    }
  }
  return { material: material(doc, prim.material, images), skin: skinned ? skinIndex : NONE, stride: skinned ? 17 : 12, verts, ids: faces, lo, hi };
}

function walk(doc, index, parent, out, images, skins) {
  const node = doc.nodes[index];
  const world = mat4Mul(parent, nodeMatrix(node));
  if (node.mesh !== undefined) {
    const skin = node.skin !== undefined ? skins[node.skin] : null;
    for (const prim of doc.meshes[node.mesh].primitives) {
      const p = primitive(doc, prim, world, images, node.skin ?? NONE, skin);
      if (p) out.push(p);
    }
  }
  for (const child of node.children ?? []) walk(doc, child, world, out, images, skins);
}

function sample(channel, time, n, rotation) {
  const { times, values, interp } = channel;
  const last = times.length - 1;
  if (time <= times[0]) return read(values, 0, n, interp);
  if (time >= times[last]) return read(values, last, n, interp);
  let k = 0;
  while (k < last - 1 && times[k + 1] <= time) k += 1;
  const dt = times[k + 1] - times[k];
  const t = dt > 0 ? (time - times[k]) / dt : 0;
  const a = read(values, k, n, interp);
  const b = read(values, k + 1, n, interp);
  if (interp === "STEP") return a;
  if (interp === "CUBICSPLINE") {
    const outTan = values.subarray((k * 3 + 2) * n, (k * 3 + 3) * n);
    const inTan = values.subarray(((k + 1) * 3) * n, ((k + 1) * 3 + 1) * n);
    const t2 = t * t, t3 = t2 * t;
    const h00 = 2 * t3 - 3 * t2 + 1, h10 = t3 - 2 * t2 + t, h01 = -2 * t3 + 3 * t2, h11 = t3 - t2;
    const out = a.map((v, i) => h00 * v + h10 * dt * outTan[i] + h01 * b[i] + h11 * dt * inTan[i]);
    return rotation ? unitQuat(out) : out;
  }
  if (rotation) return slerp(a, b, t);
  return a.map((v, i) => v + (b[i] - v) * t);
}

function read(values, k, n, interp) {
  const at = interp === "CUBICSPLINE" ? (k * 3 + 1) * n : k * n;
  return Array.from(values.subarray(at, at + n));
}

function clips(doc, skins, rate) {
  const out = [];
  (doc.animations ?? []).forEach((anim, ai) => {
    const byNode = new Map();
    let t0 = Infinity, t1 = -Infinity;
    for (const ch of anim.channels) {
      if (ch.target.node === undefined) continue;
      if (ch.target.path === "weights") { warn("animation " + ai + " animates morph weights; dropped"); continue; }
      const s = anim.samplers[ch.sampler];
      const times = accessor(doc, s.input).data;
      const values = accessor(doc, s.output).data;
      t0 = Math.min(t0, times[0]);
      t1 = Math.max(t1, times[times.length - 1]);
      if (!byNode.has(ch.target.node)) byNode.set(ch.target.node, {});
      byNode.get(ch.target.node)[ch.target.path] = { times, values, interp: s.interpolation ?? "LINEAR" };
    }
    if (!Number.isFinite(t0)) return;
    for (const node of byNode.keys()) {
      if (!skins.some((s) => s.byNode.has(node))) warn("animation " + ai + " drives node " + node + ", which is no joint; dropped");
    }
    skins.forEach((skin, si) => {
      if (!skin.joints.some((j) => byNode.has(j.node))) return;
      const samples = Math.max(1, Math.round((t1 - t0) * rate) + 1);
      const keys = [];
      for (let s = 0; s < samples; s += 1) {
        const time = t0 + s / rate;
        for (const j of skin.joints) {
          const ch = byNode.get(j.node) ?? {};
          const t = ch.translation ? sample(ch.translation, time, 3, false) : j.rest.t;
          const r = ch.rotation ? sample(ch.rotation, time, 4, true) : j.rest.r;
          const sc = ch.scale ? sample(ch.scale, time, 3, false) : j.rest.s;
          keys.push(...t, ...r, ...sc);
        }
      }
      out.push({ name: anim.name ?? "clip" + ai, skin: si, rate, samples, joints: skin.joints.length, keys });
    });
  });
  return out;
}

function encode(prims, skins, clipList) {
  const words = 5
    + prims.reduce((s, p) => s + 21 + p.verts.length * p.stride + p.ids.length, 0)
    + skins.reduce((s, k) => s + 1 + k.joints.length * (NAME_WORDS + 43), 0)
    + clipList.reduce((s, c) => s + NAME_WORDS + 5 + c.keys.length, 0);
  const out = Buffer.alloc(words * 4);
  let at = 0;
  const u32 = (v) => { out.writeUInt32LE(v >>> 0, at); at += 4; };
  const f32 = (v) => { out.writeFloatLE(v, at); at += 4; };
  const name = (s) => {
    const b = Buffer.alloc(NAME_WORDS * 4);
    Buffer.from(s, "utf8").copy(b, 0, 0, NAME_WORDS * 4 - 1);
    b.copy(out, at);
    at += NAME_WORDS * 4;
  };
  const rows = (m) => { for (let r = 0; r < 4; r += 1) for (let c = 0; c < 4; c += 1) f32(m[c * 4 + r]); };
  u32(FORMAT_MAGIC);
  u32(FORMAT_VERSION);
  u32(prims.length);
  for (const p of prims) {
    const m = p.material;
    u32(p.verts.length);
    u32(p.ids.length / 3);
    u32(p.skin);
    u32(p.stride);
    for (const c of m.base) f32(c);
    f32(m.metallic);
    f32(m.roughness);
    u32(m.flags);
    f32(m.normalScale);
    for (const c of m.emissive) f32(c);
    for (const v of p.lo) f32(v);
    for (const v of p.hi) f32(v);
    for (const v of p.verts) {
      for (let j = 0; j < 12; j += 1) f32(v[j]);
      if (p.stride === 17) {
        u32(v[12]);
        for (let j = 13; j < 17; j += 1) f32(v[j]);
      }
    }
    for (const t of p.ids) u32(t);
  }
  u32(skins.length);
  for (const k of skins) {
    u32(k.joints.length);
    for (const j of k.joints) {
      name(j.name);
      u32(j.parent);
      rows(j.pre);
      for (const v of j.rest.t) f32(v);
      for (const v of j.rest.r) f32(v);
      for (const v of j.rest.s) f32(v);
      rows(j.bind);
    }
  }
  u32(clipList.length);
  for (const c of clipList) {
    name(c.name);
    u32(c.skin);
    u32(c.rate);
    u32(c.samples);
    u32(c.joints);
    u32(c.keys.length / 10);
    for (const v of c.keys) f32(v);
  }
  return out;
}

function imageBytes(doc, index) {
  const img = doc.images[index];
  if (img.bufferView !== undefined) {
    const { view } = viewOf(doc, img.bufferView);
    return { bytes: Buffer.from(view.buffer, view.byteOffset, view.byteLength), ext: MIME[img.mimeType] ?? ".bin" };
  }
  const inline = dataUri(img.uri);
  if (inline) return { bytes: inline.bytes, ext: MIME[inline.mime] ?? ".bin" };
  const path = join(doc.dir, decodeURIComponent(img.uri));
  return { bytes: readFileSync(path), ext: extname(path) || ".bin" };
}

function main(argv) {
  let rate = 30;
  const args = [];
  for (let i = 0; i < argv.length; i += 1) {
    if (argv[i] === "--rate") {
      rate = Number(argv[++i]);
      if (!(rate >= 1 && rate <= 240)) fail("--rate takes samples per second from 1 to 240");
    } else {
      args.push(argv[i]);
    }
  }
  if (args.length < 1 || args.length > 2) fail("usage: bun tools/glb2mesh.js [--rate N] model.glb|model.gltf [model.mesh]");
  const input = resolve(args[0]);
  const output = resolve(args[1] ?? join(dirname(input), basename(input, extname(input)) + ".mesh"));
  const doc = open(input);
  const skins = (doc.skins ?? []).map((s, i) => skinOf(doc, s, i));
  const prims = [];
  const images = [];
  const scene = doc.scenes[doc.scene ?? 0];
  for (const root of scene.nodes ?? []) walk(doc, root, IDENTITY, prims, images, skins);
  if (prims.length === 0) fail("the scene has no triangles");
  const clipList = clips(doc, skins, rate);
  writeFileSync(output, encode(prims, skins, clipList));
  const total = prims.reduce((s, p) => s + p.ids.length / 3, 0);
  const unique = prims.reduce((s, p) => s + p.verts.length, 0);
  console.log(output + ": " + prims.length + " primitives, " + total + " triangles, " + unique + " vertices, " + skins.length + " skins, "
    + clipList.length + " clips" + (clipList.length ? " at " + rate + " Hz" : ""));
  const written = new Set();
  const todo = [];
  for (const { image, material: mat, kind } of images) {
    const name = join(dirname(output), "m" + mat + "." + kind);
    if (written.has(name)) continue;
    written.add(name);
    const { bytes, ext } = imageBytes(doc, image);
    writeFileSync(name + ext, bytes);
    console.log(name + ext + ": " + bytes.length + " bytes");
    todo.push(name + ext);
  }
  if (todo.length > 0) console.log("textures: bun tools/img2tex.js --size 512 " + todo.map((t) => relative(process.cwd(), t)).join(" "));
}

main(process.argv.slice(2));
