import { readdirSync, statSync, mkdirSync, copyFileSync, existsSync, readFileSync, unlinkSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { join, relative, dirname, basename, extname, resolve } from "node:path";

const ROOT = resolve(import.meta.dir, "..");
const IMAGES = new Set([".png", ".jpg", ".jpeg", ".webp", ".avif", ".gif", ".bmp"]);
const MODELS = new Set([".glb", ".gltf"]);
const MESH_TEXTURE_SIZE = 512;
const MESH_VERSION = 5;

function meshCurrent(path) {
  if (!existsSync(path)) return false;
  const head = Buffer.alloc(8);
  const fd = require("node:fs").openSync(path, "r");
  const n = require("node:fs").readSync(fd, head, 0, 8, 0);
  require("node:fs").closeSync(fd);
  return n === 8 && head.readUInt32LE(4) === MESH_VERSION;
}

function fail(message) {
  console.error("import: " + message);
  process.exit(1);
}

function args(argv) {
  const opts = { source: join(ROOT, "assets", "source"), out: join(ROOT, "assets", "imported"), size: 0, force: false, dry: false };
  for (let i = 0; i < argv.length; i += 1) {
    const a = argv[i];
    if (a === "--source") opts.source = resolve(argv[++i]);
    else if (a === "--out") opts.out = resolve(argv[++i]);
    else if (a === "--size") opts.size = Number(argv[++i]);
    else if (a === "--force") opts.force = true;
    else if (a === "--dry") opts.dry = true;
    else fail("usage: bun tools/import.js [--source dir] [--out dir] [--size N] [--force] [--dry]");
  }
  if (opts.size && (!(opts.size >= 2) || (opts.size & (opts.size - 1)) !== 0)) fail("--size takes a power of two of at least 2");
  return opts;
}

function walk(dir, out = []) {
  for (const name of readdirSync(dir)) {
    const path = join(dir, name);
    if (statSync(path).isDirectory()) walk(path, out);
    else if (name !== ".gitkeep") out.push(path);
  }
  return out;
}

function gltfDependencies(path) {
  const deps = new Set();
  try {
    const doc = JSON.parse(readFileSync(path, "utf8"));
    for (const item of [...(doc.buffers ?? []), ...(doc.images ?? [])]) {
      if (item.uri && !/^data:/.test(item.uri)) deps.add(resolve(dirname(path), decodeURIComponent(item.uri)));
    }
  } catch (e) {
    console.error("import: cannot read " + path + ": " + e.message);
  }
  return deps;
}

function fresh(source, outputs, force) {
  if (force || outputs.length === 0) return false;
  const since = statSync(source).mtimeMs;
  return outputs.every((o) => existsSync(o) && statSync(o).mtimeMs >= since);
}

function run(script, list) {
  const r = spawnSync("bun", [join(ROOT, "tools", script), ...list], { encoding: "utf8" });
  if (r.stdout) process.stdout.write(r.stdout);
  if (r.stderr) process.stderr.write(r.stderr);
  return r.status === 0;
}

function meshTextures(dir) {
  if (!existsSync(dir)) return [];
  return readdirSync(dir).filter((n) => /^m\d+\.\w+\.\w+$/.test(n)).map((n) => join(dir, n));
}

function main(argv) {
  const opts = args(argv);
  if (!existsSync(opts.source)) fail("no source directory " + opts.source);
  const files = walk(opts.source);
  const consumed = new Set();
  for (const f of files) if (extname(f).toLowerCase() === ".gltf") for (const d of gltfDependencies(f)) consumed.add(d);
  const textures = [];
  let done = 0, skipped = 0, failed = 0;
  const plan = (what) => { if (opts.dry) console.log("would " + what); return !opts.dry; };
  for (const src of files) {
    if (consumed.has(src)) continue;
    const rel = relative(opts.source, src);
    const ext = extname(src).toLowerCase();
    const outDir = join(opts.out, dirname(rel));
    const stem = join(outDir, basename(src, extname(src)));
    if (MODELS.has(ext)) {
      const mesh = join(stem, basename(src, extname(src)) + ".mesh");
      const texes = meshTextures(stem).filter((t) => t.endsWith(".tex"));
      const pending = meshTextures(stem).filter((t) => IMAGES.has(extname(t).toLowerCase()));
      if (fresh(src, [mesh, ...texes], opts.force) && pending.length === 0 && meshCurrent(mesh)) { skipped += 1; continue; }
      if (!plan("convert " + rel + " -> " + relative(ROOT, mesh))) continue;
      mkdirSync(stem, { recursive: true });
      if (!run("glb2mesh.js", [src, mesh])) { failed += 1; continue; }
      done += 1;
      for (const image of meshTextures(stem).filter((t) => IMAGES.has(extname(t).toLowerCase()))) {
        textures.push({ input: image, size: opts.size || MESH_TEXTURE_SIZE, intermediate: true });
      }
    } else if (IMAGES.has(ext)) {
      const tex = stem + ".tex";
      if (fresh(src, [tex], opts.force)) { skipped += 1; continue; }
      if (!plan("convert " + rel + " -> " + relative(ROOT, tex))) continue;
      mkdirSync(outDir, { recursive: true });
      textures.push({ input: src, output: tex, size: opts.size, intermediate: false });
    } else {
      const copy = stem + ext;
      if (fresh(src, [copy], opts.force)) { skipped += 1; continue; }
      if (!plan("copy " + rel)) continue;
      mkdirSync(outDir, { recursive: true });
      copyFileSync(src, copy);
      console.log(relative(ROOT, copy) + ": copied");
      done += 1;
    }
  }
  const bySize = new Map();
  for (const t of textures) {
    if (!bySize.has(t.size)) bySize.set(t.size, []);
    bySize.get(t.size).push(t);
  }
  for (const [size, batch] of bySize) {
    const ok = run("img2tex.js", [...(size ? ["--size", String(size)] : []), ...batch.map((t) => t.input)]);
    for (const t of batch) {
      const made = t.input.replace(/\.[^./\\]+$/, "") + ".tex";
      if (!existsSync(made)) { failed += 1; continue; }
      if (t.output && t.output !== made) copyFileSync(made, t.output);
      if (t.intermediate) unlinkSync(t.input);
      done += 1;
    }
    if (!ok) console.error("import: the texture batch reported errors");
  }
  console.log("import: " + done + " done, " + skipped + " up to date, " + failed + " failed");
  process.exit(failed === 0 ? 0 : 1);
}

main(process.argv.slice(2));
