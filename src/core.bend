import Base

def sel(~A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def Got(-A: Type) -> Type:
  Result<&1, &1, U32 & String, A>

def unit(+v: F32) -> U32:
  F32.to_u32((255.0 * F32.clamp(v, 0.0, 1.0) : F32))

def pack(+r: F32, +g: F32, +b: F32) -> U32:
  (unit(r) << 16n .|. unit(g) << 8n .|. unit(b) : U32)

type Box is Data:
  Box{+x0: F32, +y0: F32, +z0: F32, +x1: F32, +y1: F32, +z1: F32}

def Box.area(+x0: F32, +y0: F32, +z0: F32, +x1: F32, +y1: F32, +z1: F32) -> F32:
  +dx = F32.max(0.0, (x1 - x0 : F32))
  +dy = F32.max(0.0, (y1 - y0 : F32))
  +dz = F32.max(0.0, (z1 - z0 : F32))
  (2.0 * (dx * dy + dy * dz + dz * dx) : F32)

type Vec2 is Data:
  Vec2{x: F32, y: F32}

type Vec3 is Data:
  Vec3{x: F32, y: F32, z: F32}

type Vec4 is Data:
  Vec4{x: F32, y: F32, z: F32, w: F32}

type Quat is Data:
  Quat{x: F32, y: F32, z: F32, w: F32}

type Mat3 is Data:
  Mat3{a: Vec3, b: Vec3, c: Vec3}

type Mat4 is Data:
  Mat4{a: Vec4, b: Vec4, c: Vec4, d: Vec4}

type Xform is Data:
  Xform{pos: Vec3, rot: Quat, scl: Vec3}

type Tree4<-V: Data> is Data:
  T4Nil{}
  T4Leaf{v: V}
  T4Qua{a: Tree4<V>, b: Tree4<V>, c: Tree4<V>, d: Tree4<V>}

type Trs is Data:
  Trs{t: Vec3, r: Quat, s: Vec3}

def Words.rev(bytes: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match bytes:
    case b0 <> b1 <> b2 <> b3 <> rest:
      Words.rev(rest, (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216 : U32) <> acc)
    case _:
      acc

def Words.of(bytes: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, Words.rev(bytes, Nil{}))

def Bits.f32(+w: U32) -> F32:
  +e = ((w / 8388608 : U32) .&. 255 : U32)
  +m = ((w .&. 8388607 : U32) .|. sel(~U32, U32.is_eq(e, 0), 0, 8388608) : U32)
  +p = sel(~F32, U32.is_eq(e, 0), (0.0 - 149.0 : F32), (U32.to_f32(e) - 150.0 : F32))
  +v = (U32.to_f32(m) * F32.pow(2.0, p) : F32)
  sel(~F32, (w >= 2147483648 : U32), (0.0 - v : F32), v)

def Words.drop(k: Nat, ws: List<&2, U32>) -> List<&2, U32>:
  match k ws:
    case 0n rest:
      rest
    case 1n+j w <> rest:
      Words.drop(j, rest)
    case _ _:
      Nil{}

def Tree4.bits(+i: U32, k: Nat) -> U32:
  match k:
    case 0n:
      0
    case 1n+m:
      (U32.shrn(i, Nat.double(m)) .&. 3 : U32)

def Tree4.get(-V: Data, +k: Nat, sel: U32, t: Tree4<V>, +i: U32, d: V) -> V:
  match k sel t:
    case _ _ T4Nil{}:
      d
    case _ _ T4Leaf{v}:
      v
    case 0n _ T4Qua{_, _, _, _}:
      d
    case 1n+j 0 T4Qua{a, _, _, _}:
      Tree4.get(V, j, Tree4.bits(i, j), a, i, d)
    case 1n+j 1 T4Qua{_, b, _, _}:
      Tree4.get(V, j, Tree4.bits(i, j), b, i, d)
    case 1n+j 2 T4Qua{_, _, c, _}:
      Tree4.get(V, j, Tree4.bits(i, j), c, i, d)
    case 1n+j _ T4Qua{_, _, _, e}:
      Tree4.get(V, j, Tree4.bits(i, j), e, i, d)

def Tree4.put(-V: Data, +k: Nat, sel: U32, t: Tree4<V>, +i: U32, v: V) -> Tree4<V>:
  match k sel t:
    case 0n _ _:
      T4Leaf{v}
    case 1n+j 0 T4Qua{a, b, c, e}:
      T4Qua{Tree4.put(V, j, Tree4.bits(i, j), a, i, v), b, c, e}
    case 1n+j 1 T4Qua{a, b, c, e}:
      T4Qua{a, Tree4.put(V, j, Tree4.bits(i, j), b, i, v), c, e}
    case 1n+j 2 T4Qua{a, b, c, e}:
      T4Qua{a, b, Tree4.put(V, j, Tree4.bits(i, j), c, i, v), e}
    case 1n+j _ T4Qua{a, b, c, e}:
      T4Qua{a, b, c, Tree4.put(V, j, Tree4.bits(i, j), e, i, v)}
    case 1n+j 0 _:
      T4Qua{Tree4.put(V, j, Tree4.bits(i, j), T4Nil{}, i, v), T4Nil{}, T4Nil{}, T4Nil{}}
    case 1n+j 1 _:
      T4Qua{T4Nil{}, Tree4.put(V, j, Tree4.bits(i, j), T4Nil{}, i, v), T4Nil{}, T4Nil{}}
    case 1n+j 2 _:
      T4Qua{T4Nil{}, T4Nil{}, Tree4.put(V, j, Tree4.bits(i, j), T4Nil{}, i, v), T4Nil{}}
    case 1n+j _ _:
      T4Qua{T4Nil{}, T4Nil{}, T4Nil{}, Tree4.put(V, j, Tree4.bits(i, j), T4Nil{}, i, v)}

def Tree4.at(-V: Data, +k: Nat, t: Tree4<V>, +i: U32, d: V) -> V:
  Tree4.get(V, k, Tree4.bits(i, k), t, i, d)

def Tree4.set(-V: Data, +k: Nat, t: Tree4<V>, +i: U32, v: V) -> Tree4<V>:
  Tree4.put(V, k, Tree4.bits(i, k), t, i, v)

def Tree4.fit.go(f: Nat, +n: U32, +k: Nat) -> Nat:
  match f:
    case 0n:
      k
    case 1n+p:
      Tree4.fit.go(p, n, Nat.add(k, U32.to_nat(sel(~U32, (U32.shln(1, Nat.double(k)) < n : U32), 1, 0))))

def Tree4.fit(+n: U32) -> Nat:
  Tree4.fit.go(16n, n, 0n)

def none() -> U32:
  4294967295

def fb(+w: U32) -> F32:
  Bits.f32(w)

def Box.empty() -> Box:
  Box{1000000000.0, 1000000000.0, 1000000000.0, (0.0 - 1000000000.0 : F32), (0.0 - 1000000000.0 : F32), (0.0 - 1000000000.0 : F32)}

def Box.add(b: Box, +x: F32, +y: F32, +z: F32) -> Box:
  Box{x0, y0, z0, x1, y1, z1} = b
  Box{F32.min(x0, x), F32.min(y0, y), F32.min(z0, z), F32.max(x1, x), F32.max(y1, y), F32.max(z1, z)}

def Array.depth(fuel: Nat, enough: Bool, +n: U32, +have: U32, +d: Nat) -> Nat:
  match fuel enough:
    case 0n _:
      d
    case _ True{}:
      d
    case 1n+f False{}:
      +have2 = (have * 2 : U32)
      Array.depth(f, (have2 >= n : U32), n, have2, 1n+d)

def Pairs.level(~A: Data, ~join: A -> A -> A, ~lone: A -> A, xs: List<&2, A>, acc: List<&2, A>) -> List<&2, A>:
  match xs:
    case a <> b <> rest:
      Pairs.level(~A, ~join, ~lone, rest, join(a, b) <> acc)
    case a <> Nil{}:
      lone(a) <> acc
    case Nil{}:
      acc

def Pairs.up(~A: Data, ~join: A -> A -> A, ~lone: A -> A, ~none: A, k: Nat, xs: List<&2, A>) -> A:
  match k xs:
    case _ t <> Nil{}:
      t
    case 0n t <> _:
      t
    case 0n Nil{}:
      none
    case 1n+j other:
      Pairs.up(~A, ~join, ~lone, ~none, j, List.reverse(&2, A, Pairs.level(~A, ~join, ~lone, other, Nil{})))

def Vec3.zero() -> Vec3:
  Vec3{0.0, 0.0, 0.0}

def Vec3.add(+a: Vec3, +b: Vec3) -> Vec3:
  Vec3{ax, ay, az} = a
  Vec3{bx, by, bz} = b
  Vec3{(ax + bx : F32), (ay + by : F32), (az + bz : F32)}

def Vec3.mul(+a: Vec3, +b: Vec3) -> Vec3:
  Vec3{ax, ay, az} = a
  Vec3{bx, by, bz} = b
  Vec3{(ax * bx : F32), (ay * by : F32), (az * bz : F32)}

def Vec3.scale(+a: Vec3, +s: F32) -> Vec3:
  Vec3{x, y, z} = a
  Vec3{(x * s : F32), (y * s : F32), (z * s : F32)}

def Vec3.dot(+a: Vec3, +b: Vec3) -> F32:
  Vec3{ax, ay, az} = a
  Vec3{bx, by, bz} = b
  (ax * bx + ay * by + az * bz : F32)

def Vec3.normalize(+a: Vec3) -> Vec3:
  Vec3.scale(a, (1.0 / F32.max(0.00001, F32.sqrt(Vec3.dot(a, a))) : F32))

def Vec3.mix(+a: Vec3, +b: Vec3, +t: F32) -> Vec3:
  Vec3{ax, ay, az} = a
  Vec3{bx, by, bz} = b
  Vec3{(ax + (bx - ax) * t : F32), (ay + (by - ay) * t : F32), (az + (bz - az) * t : F32)}

def Vec4.of(+v: Vec3, +w: F32) -> Vec4:
  Vec3{x, y, z} = v
  Vec4{x, y, z, w}

def Vec4.xyz(+a: Vec4) -> Vec3:
  Vec4{x, y, z, _} = a
  Vec3{x, y, z}

def Vec4.dot(+a: Vec4, +b: Vec4) -> F32:
  Vec4{ax, ay, az, aw} = a
  Vec4{bx, by, bz, bw} = b
  (ax * bx + ay * by + az * bz + aw * bw : F32)

def Quat.scale(+q: Quat, +s: F32) -> Quat:
  Quat{x, y, z, w} = q
  Quat{(x * s : F32), (y * s : F32), (z * s : F32), (w * s : F32)}

def Quat.add(+p: Quat, +q: Quat) -> Quat:
  Quat{px, py, pz, pw} = p
  Quat{qx, qy, qz, qw} = q
  Quat{(px + qx : F32), (py + qy : F32), (pz + qz : F32), (pw + qw : F32)}

def Quat.dot(+p: Quat, +q: Quat) -> F32:
  Quat{px, py, pz, pw} = p
  Quat{qx, qy, qz, qw} = q
  (px * qx + py * qy + pz * qz + pw * qw : F32)

def Quat.normalize(+q: Quat) -> Quat:
  Quat.scale(q, (1.0 / F32.max(0.00001, F32.sqrt(Quat.dot(q, q))) : F32))

def Quat.slerp(+p: Quat, +q: Quat, +t: F32) -> Quat:
  +d0 = Quat.dot(p, q)
  +flip = sel(~F32, (d0 < 0.0 : F32), (0.0 - 1.0 : F32), 1.0)
  +d = F32.clamp((d0 * flip : F32), (0.0 - 1.0 : F32), 1.0)
  +theta = F32.acos(d)
  +s = F32.sin(theta)
  +tight = (s < 0.001 : F32)
  +wp = sel(~F32, tight, (1.0 - t : F32), (F32.sin(((1.0 - t) * theta : F32)) / s : F32))
  +wq = sel(~F32, tight, t, (F32.sin((t * theta : F32)) / s : F32))
  Quat.normalize(Quat.add(Quat.scale(p, wp), Quat.scale(q, (wq * flip : F32))))

def Quat.to_mat3(+q: Quat) -> Mat3:
  Quat{x, y, z, w} = q
  +xx = (x * x : F32)
  +yy = (y * y : F32)
  +zz = (z * z : F32)
  +xy = (x * y : F32)
  +xz = (x * z : F32)
  +yz = (y * z : F32)
  +wx = (w * x : F32)
  +wy = (w * y : F32)
  +wz = (w * z : F32)
  Mat3{Vec3{(1.0 - 2.0 * (yy + zz) : F32), (2.0 * (xy - wz) : F32), (2.0 * (xz + wy) : F32)},
    Vec3{(2.0 * (xy + wz) : F32), (1.0 - 2.0 * (xx + zz) : F32), (2.0 * (yz - wx) : F32)},
    Vec3{(2.0 * (xz - wy) : F32), (2.0 * (yz + wx) : F32), (1.0 - 2.0 * (xx + yy) : F32)}}

def Mat4.id() -> Mat4:
  Mat4{Vec4{1.0, 0.0, 0.0, 0.0}, Vec4{0.0, 1.0, 0.0, 0.0}, Vec4{0.0, 0.0, 1.0, 0.0}, Vec4{0.0, 0.0, 0.0, 1.0}}

def Mat4.transpose(+m: Mat4) -> Mat4:
  Mat4{a, b, c, d} = m
  Vec4{ax, ay, az, aw} = a
  Vec4{bx, by, bz, bw} = b
  Vec4{cx, cy, cz, cw} = c
  Vec4{dx, dy, dz, dw} = d
  Mat4{Vec4{ax, bx, cx, dx}, Vec4{ay, by, cy, dy}, Vec4{az, bz, cz, dz}, Vec4{aw, bw, cw, dw}}

def Mat4.mul_vec(+m: Mat4, +v: Vec4) -> Vec4:
  Mat4{a, b, c, d} = m
  Vec4{Vec4.dot(a, v), Vec4.dot(b, v), Vec4.dot(c, v), Vec4.dot(d, v)}

def Mat4.mul(+m: Mat4, +n: Mat4) -> Mat4:
  Mat4{a, b, c, d} = m
  +t = Mat4.transpose(n)
  Mat4{Mat4.mul_vec(t, a), Mat4.mul_vec(t, b), Mat4.mul_vec(t, c), Mat4.mul_vec(t, d)}

def Mat4.of_mat3(+m: Mat3, +pos: Vec3) -> Mat4:
  Mat3{a, b, c} = m
  Vec3{px, py, pz} = pos
  Mat4{Vec4.of(a, px), Vec4.of(b, py), Vec4.of(c, pz), Vec4{0.0, 0.0, 0.0, 1.0}}

def Mat4.transform_point(+m: Mat4, +p: Vec3) -> Vec3:
  Vec4.xyz(Mat4.mul_vec(m, Vec4.of(p, 1.0)))

def Mat4.transform_dir(+m: Mat4, +v: Vec3) -> Vec3:
  Vec4.xyz(Mat4.mul_vec(m, Vec4.of(v, 0.0)))

def Mat4.move(+x: F32, +y: F32, +z: F32) -> Mat4:
  Mat4{Vec4{1.0, 0.0, 0.0, x}, Vec4{0.0, 1.0, 0.0, y}, Vec4{0.0, 0.0, 1.0, z}, Vec4{0.0, 0.0, 0.0, 1.0}}

def Mat4.scale(+s: F32) -> Mat4:
  Mat4{Vec4{s, 0.0, 0.0, 0.0}, Vec4{0.0, s, 0.0, 0.0}, Vec4{0.0, 0.0, s, 0.0}, Vec4{0.0, 0.0, 0.0, 1.0}}

def Mat4.turn_x(+a: F32) -> Mat4:
  +c = F32.cos(a)
  +s = F32.sin(a)
  Mat4{Vec4{1.0, 0.0, 0.0, 0.0}, Vec4{0.0, c, (0.0 - s : F32), 0.0}, Vec4{0.0, s, c, 0.0}, Vec4{0.0, 0.0, 0.0, 1.0}}

def Mat4.turn_y(+a: F32) -> Mat4:
  +c = F32.cos(a)
  +s = F32.sin(a)
  Mat4{Vec4{c, 0.0, s, 0.0}, Vec4{0.0, 1.0, 0.0, 0.0}, Vec4{(0.0 - s : F32), 0.0, c, 0.0}, Vec4{0.0, 0.0, 0.0, 1.0}}

def Xform.to_mat4.go(+m: Mat3, +scl: Vec3, +pos: Vec3) -> Mat4:
  Mat3{a, b, c} = m
  Mat4.of_mat3(Mat3{Vec3.mul(a, scl), Vec3.mul(b, scl), Vec3.mul(c, scl)}, pos)

def Xform.to_mat4(+x: Xform) -> Mat4:
  Xform{pos, rot, scl} = x
  Xform.to_mat4.go(Quat.to_mat3(rot), scl, pos)

def Trs.mix(+a: Trs, +b: Trs, +t: F32) -> Trs:
  Trs{at, ar, as} = a
  Trs{bt, br, bs} = b
  Trs{Vec3.mix(at, bt, t), Quat.slerp(ar, br, t), Vec3.mix(as, bs, t)}

def Trs.to_mat4(+k: Trs) -> Mat4:
  Trs{t, r, s} = k
  Xform.to_mat4(Xform{t, r, s})

type V is Data:
  V{+px: F32, +py: F32, +pz: F32, +nx: F32, +ny: F32, +nz: F32, +u: F32, +v: F32}

type Tex is Data:
  TFlat{+c: U32}
  TLeaf{+a: U32, +b: U32, +c: U32, +d: U32}
  TNode{tl: Tex, tr: Tex, bl: Tex, br: Tex}

type Mats is Data:
  MtNone{}
  MtLeaf{+pw: U32, base: Tex, +mpw: U32, mr: Tex, +npw: U32, nrm: Tex, +metal: F32, +rough: F32, +ns: F32, +er: F32, +eg: F32, +eb: F32}
  MtNode{l: Mats, r: Mats}

type Em is Data:
  Em{+le: F32, +er: F32, +eg: F32, +eb: F32}

type Portal is Data:
  Portal{+x0: F32, +z0: F32, +x1: F32, +z1: F32, +y: F32}

type Mat is Data:
  Mat{+col: U32, +metal: F32, +rough: F32, +le: F32}

type Vert is Data:
  Vert{p: Vec3, n: Vec3, uv: Vec2, j: U32, w: Vec4}

type Prim is Data:
  Prim{+mat: Mat, +skin: U32, +depth: Nat, verts: Tree4<Vert>, ids: List<&2, U32>}

type Joint is Data:
  Joint{name: String, parent: U32, pre: Mat4, rest: Xform, bind: Mat4}

type Skin is Data:
  Skin{joints: List<&2, Joint>}

type ClipHead is Data:
  ClipHead{name: String, skin: U32, rate: U32, samples: U32, joints: U32}

type Clip is Data:
  Clip{name: String, skin: U32, rate: U32, samples: U32, joints: U32, keys: List<&2, Trs>}

type Mesh is Data:
  Mesh{prims: List<&2, Prim>, skins: List<&2, Skin>, clips: List<&2, Clip>, ems: List<&2, Em>}

def ClipHead.none() -> ClipHead:
  ClipHead{"", none(), 0, 0, 0}

def Name.put(zero: Bool, +c: U32, acc: List<&2, Char>) -> List<&2, Char>:
  match zero:
    case True{}:
      acc
    case False{}:
      Char.from_u32(c) <> acc

def Name.word(+w: U32, acc: List<&2, Char>) -> List<&2, Char>:
  +b0 = (w .&. 255 : U32)
  +b1 = ((w >> 8n) .&. 255 : U32)
  +b2 = ((w >> 16n) .&. 255 : U32)
  +b3 = ((w >> 24n) .&. 255 : U32)
  Name.put(U32.is_eq(b3, 0), b3, Name.put(U32.is_eq(b2, 0), b2, Name.put(U32.is_eq(b1, 0), b1, Name.put(U32.is_eq(b0, 0), b0, acc))))

def Name.of(+w0: U32, +w1: U32, +w2: U32, +w3: U32, +w4: U32, +w5: U32, +w6: U32, +w7: U32) -> String:
  String.from_list(List.reverse(&2, Char, Name.word(w7, Name.word(w6, Name.word(w5, Name.word(w4, Name.word(w3, Name.word(w2, Name.word(w1, Name.word(w0, Nil{}))))))))))

def Mesh.mat4(+a0: U32, +a1: U32, +a2: U32, +a3: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, +c0: U32, +c1: U32, +c2: U32, +c3: U32, +d0: U32, +d1: U32, +d2: U32, +d3: U32) -> Mat4:
  Mat4{Vec4{fb(a0), fb(a1), fb(a2), fb(a3)}, Vec4{fb(b0), fb(b1), fb(b2), fb(b3)}, Vec4{fb(c0), fb(c1), fb(c2), fb(c3)}, Vec4{fb(d0), fb(d1), fb(d2), fb(d3)}}

def Skin.close(cur: List<&2, Joint>, acc: List<&2, Skin>) -> List<&2, Skin>:
  match cur:
    case Nil{}:
      acc
    case other:
      Skin{List.reverse(&2, Joint, other)} <> acc

def Mesh.skins(words: List<&2, U32>, sl: Nat, jl: Nat, cur: List<&2, Joint>, acc: List<&2, Skin>) -> List<&2, Skin> & List<&2, U32>:
  match words sl jl:
    case rest 0n 0n:
      (List.reverse(&2, Skin, Skin.close(cur, acc)), rest)
    case jc <> rest 1n+s 0n:
      Mesh.skins(rest, s, U32.to_nat(jc), Nil{}, Skin.close(cur, acc))
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> par
      <> pa0 <> pa1 <> pa2 <> pa3 <> pb0 <> pb1 <> pb2 <> pb3 <> pc0 <> pc1 <> pc2 <> pc3 <> pd0 <> pd1 <> pd2 <> pd3
      <> tx <> ty <> tz <> rx <> ry <> rz <> rw <> sx <> sy <> sz
      <> ba0 <> ba1 <> ba2 <> ba3 <> bb0 <> bb1 <> bb2 <> bb3 <> bc0 <> bc1 <> bc2 <> bc3 <> bd0 <> bd1 <> bd2 <> bd3
      <> rest _ 1n+k:
      Mesh.skins(rest, sl, k, Joint{Name.of(n0, n1, n2, n3, n4, n5, n6, n7), par, Mesh.mat4(pa0, pa1, pa2, pa3, pb0, pb1, pb2, pb3, pc0, pc1, pc2, pc3, pd0, pd1, pd2, pd3), Xform{Vec3{fb(tx), fb(ty), fb(tz)}, Quat{fb(rx), fb(ry), fb(rz), fb(rw)}, Vec3{fb(sx), fb(sy), fb(sz)}}, Mesh.mat4(ba0, ba1, ba2, ba3, bb0, bb1, bb2, bb3, bc0, bc1, bc2, bc3, bd0, bd1, bd2, bd3)} <> cur, acc)
    case _ _ _:
      (List.reverse(&2, Skin, Skin.close(cur, acc)), Nil{})

def Clip.close(cur: List<&2, Trs>, h: ClipHead, acc: List<&2, Clip>) -> List<&2, Clip>:
  match cur:
    case Nil{}:
      acc
    case other:
      ClipHead{name, skin, rate, samples, joints} = h
      Clip{name, skin, rate, samples, joints, List.reverse(&2, Trs, other)} <> acc

def Mesh.clips(words: List<&2, U32>, cl: Nat, n: Nat, h: ClipHead, cur: List<&2, Trs>, acc: List<&2, Clip>) -> List<&2, Clip> & List<&2, U32>:
  match words cl n:
    case rest 0n 0n:
      (List.reverse(&2, Clip, Clip.close(cur, h, acc)), rest)
    case n0 <> n1 <> n2 <> n3 <> n4 <> n5 <> n6 <> n7 <> sk <> rt <> sm <> jn <> kc <> rest 1n+c 0n:
      Mesh.clips(rest, c, U32.to_nat(kc), ClipHead{Name.of(n0, n1, n2, n3, n4, n5, n6, n7), sk, rt, sm, jn}, Nil{}, Clip.close(cur, h, acc))
    case tx <> ty <> tz <> rx <> ry <> rz <> rw <> sx <> sy <> sz <> rest _ 1n+k:
      Mesh.clips(rest, cl, k, h, Trs{Vec3{fb(tx), fb(ty), fb(tz)}, Quat{fb(rx), fb(ry), fb(rz), fb(rw)}, Vec3{fb(sx), fb(sy), fb(sz)}} <> cur, acc)
    case _ _ _:
      (List.reverse(&2, Clip, Clip.close(cur, h, acc)), Nil{})

def Mesh.done(prims: List<&2, Prim>, skins: List<&2, Skin>, r: List<&2, Clip> & List<&2, U32>) -> Mesh:
  (clips, _) = r
  Mesh{prims, skins, clips, Nil{}}

def Mesh.after_skins(prims: List<&2, Prim>, r: List<&2, Skin> & List<&2, U32>) -> Mesh:
  (skins, rest) = r
  match rest:
    case cc <> rest2:
      Mesh.done(prims, skins, Mesh.clips(rest2, U32.to_nat(cc), 0n, ClipHead.none(), Nil{}, Nil{}))
    case _:
      Mesh{prims, skins, Nil{}, Nil{}}

def Mesh.of(keep: Bool, prims: List<&2, Prim>, ws: List<&2, U32>) -> Mesh:
  match keep ws:
    case True{} sc <> rest:
      Mesh.after_skins(prims, Mesh.skins(rest, U32.to_nat(sc), 0n, Nil{}, Nil{}))
    case _ _:
      Mesh{prims, Nil{}, Nil{}, Nil{}}

def Load.heads(pc: Nat, ws: List<&2, U32>, box: Box, +pi: U32, flags: List<&2, U32>, +skinned: Bool) -> Box & (List<&2, U32> & Bool):
  match pc ws:
    case 0n _:
      (box, (flags, skinned))
    case 1n+p +vc <> +tc <> sk <> +st <> r <> g <> b <> a <> me <> ro <> fl <> ns <> er <> eg <> eb <> x0 <> y0 <> z0 <> x1 <> y1 <> z1 <> rest:
      Load.heads(p, Words.drop(U32.to_nat((vc * st + tc * 3 : U32)), rest), Box.add(Box.add(box, Bits.f32(x0), Bits.f32(y0), Bits.f32(z0)), Bits.f32(x1), Bits.f32(y1), Bits.f32(z1)), (pi + 1 : U32), (pi * 8 + (fl .&. 7) : U32) <> me <> ro <> ns <> er <> eg <> eb <> flags, (skinned || Bool.not(U32.is_eq(sk, 4294967295))))
    case _ _:
      (box, (flags, skinned))

type Fit is Data:
  Fit{+cx: F32, +cy: F32, +cz: F32, +s: F32, +floor: F32}

def Fit.of(b: Box) -> Fit:
  Box{x0, y0, z0, x1, y1, z1} = b
  +cx = ((x0 + x1) * 0.5 : F32)
  +cy = ((y0 + y1) * 0.5 : F32)
  +cz = ((z0 + z1) * 0.5 : F32)
  +s = (1.0 / F32.max(0.000001, F32.max((x1 - cx : F32), F32.max((y1 - cy : F32), (z1 - cz : F32)))) : F32)
  Fit{cx, cy, cz, s, ((y0 - cy) * s - 0.01 : F32)}

def Fit.floor(+f: Fit) -> F32:
  Fit{_, _, _, _, floor} = f
  floor

def Fit.id() -> Fit:
  Fit{0.0, 0.0, 0.0, 1.0, 0.0}

def Fit.mat(+f: Fit) -> Mat4:
  Fit{cx, cy, cz, s, _} = f
  Mat4{Vec4{s, 0.0, 0.0, (0.0 - cx * s : F32)}, Vec4{0.0, s, 0.0, (0.0 - cy * s : F32)}, Vec4{0.0, 0.0, s, (0.0 - cz * s : F32)}, Vec4{0.0, 0.0, 0.0, 1.0}}

def Portal.of(b: Box, +f: Fit) -> Portal:
  Box{x0, _, z0, x1, y1, z1} = b
  Fit{cx, cy, cz, s, _} = f
  Portal{((x0 - cx) * s : F32), ((z0 - cz) * s : F32), ((x1 - cx) * s : F32), ((z1 - cz) * s : F32), ((y1 - cy) * s : F32)}

def Load.put(a: Array<F32>, +i: U32, +px: U32, +py: U32, +pz: U32, +nx: U32, +ny: U32, +nz: U32, +u: U32, +v: U32) -> Array<F32>:
  +at = (8 * i : U32)
  Array.set(F32, Array.set(F32, Array.set(F32, Array.set(F32, Array.set(F32, Array.set(F32, Array.set(F32, Array.set(F32, a, at, Bits.f32(px)), (at + 1 : U32), Bits.f32(py)), (at + 2 : U32), Bits.f32(pz)), (at + 3 : U32), Bits.f32(nx)), (at + 4 : U32), Bits.f32(ny)), (at + 5 : U32), Bits.f32(nz)), (at + 6 : U32), Bits.f32(u)), (at + 7 : U32), Bits.f32(v))

def Load.verts(n: Nat, ws: List<&2, U32>, +skip: Nat, a: Array<F32>, +i: U32, keep: Bool, full: Bool, +k: Nat, rv: Tree4<Vert>) -> Array<F32> & (List<&2, U32> & Tree4<Vert>):
  match n ws keep full:
    case 0n rest _ _:
      (a, (rest, rv))
    case 1n+m px <> py <> pz <> nx <> ny <> nz <> _ <> _ <> _ <> _ <> u <> v <> rest False{} _:
      Load.verts(m, Words.drop(skip, rest), skip, Load.put(a, i, px, py, pz, nx, ny, nz, u, v), (i + 1 : U32), False{}, False{}, k, rv)
    case 1n+m +px <> +py <> +pz <> +nx <> +ny <> +nz <> _ <> _ <> _ <> _ <> +u <> +v <> rest True{} False{}:
      Load.verts(m, rest, skip, Load.put(a, i, px, py, pz, nx, ny, nz, u, v), (i + 1 : U32), True{}, False{}, k, Tree4.set(Vert, k, rv, i, Vert{Vec3{fb(px), fb(py), fb(pz)}, Vec3{fb(nx), fb(ny), fb(nz)}, Vec2{fb(u), fb(v)}, 0, Vec4{0.0, 0.0, 0.0, 0.0}}))
    case 1n+m +px <> +py <> +pz <> +nx <> +ny <> +nz <> _ <> _ <> _ <> _ <> +u <> +v <> jw <> w0 <> w1 <> w2 <> w3 <> rest True{} True{}:
      Load.verts(m, rest, skip, Load.put(a, i, px, py, pz, nx, ny, nz, u, v), (i + 1 : U32), True{}, True{}, k, Tree4.set(Vert, k, rv, i, Vert{Vec3{fb(px), fb(py), fb(pz)}, Vec3{fb(nx), fb(ny), fb(nz)}, Vec2{fb(u), fb(v)}, jw, Vec4{fb(w0), fb(w1), fb(w2), fb(w3)}}))
    case _ _ _ _:
      (a, (Nil{}, rv))

def V.h(p: Array<F32> & F32, +x: F32, +y: F32, +z: F32, +nx: F32, +ny: F32, +nz: F32, +u: F32) -> Array<F32> & V:
  match p:
    case (a, v):
      (a, V{x, y, z, nx, ny, nz, u, v})

def V.g(p: Array<F32> & F32, +at: U32, +x: F32, +y: F32, +z: F32, +nx: F32, +ny: F32, +nz: F32) -> Array<F32> & V:
  match p:
    case (a, u):
      V.h(Array.get(F32, a, (at + 7 : U32)), x, y, z, nx, ny, nz, u)

def V.f(p: Array<F32> & F32, +at: U32, +x: F32, +y: F32, +z: F32, +nx: F32, +ny: F32) -> Array<F32> & V:
  match p:
    case (a, nz):
      V.g(Array.get(F32, a, (at + 6 : U32)), at, x, y, z, nx, ny, nz)

def V.e(p: Array<F32> & F32, +at: U32, +x: F32, +y: F32, +z: F32, +nx: F32) -> Array<F32> & V:
  match p:
    case (a, ny):
      V.f(Array.get(F32, a, (at + 5 : U32)), at, x, y, z, nx, ny)

def V.d(p: Array<F32> & F32, +at: U32, +x: F32, +y: F32, +z: F32) -> Array<F32> & V:
  match p:
    case (a, nx):
      V.e(Array.get(F32, a, (at + 4 : U32)), at, x, y, z, nx)

def V.c(p: Array<F32> & F32, +at: U32, +x: F32, +y: F32) -> Array<F32> & V:
  match p:
    case (a, z):
      V.d(Array.get(F32, a, (at + 3 : U32)), at, x, y, z)

def V.b(p: Array<F32> & F32, +at: U32, +x: F32) -> Array<F32> & V:
  match p:
    case (a, y):
      V.c(Array.get(F32, a, (at + 2 : U32)), at, x, y)

def V.a(p: Array<F32> & F32, +at: U32) -> Array<F32> & V:
  match p:
    case (a, x):
      V.b(Array.get(F32, a, (at + 1 : U32)), at, x)

def V.at(a: Array<F32>, +i: U32) -> Array<F32> & V:
  V.a(Array.get(F32, a, (8 * i : U32)), (8 * i : U32))

def V.fit(v: V, +f: Fit) -> V:
  V{x, y, z, nx, ny, nz, u, vv} = v
  Fit{cx, cy, cz, s, _} = f
  V{((x - cx) * s : F32), ((y - cy) * s : F32), ((z - cz) * s : F32), nx, ny, nz, u, vv}

def Em.lum(+r: F32, +g: F32, +b: F32) -> F32:
  (0.2126 * r + 0.7152 * g + 0.0722 * b : F32)

type Sum is Data:
  Sum{t: Tex, +c: U32, flat: Bool}

def Tex.leaf.go(same: Bool, +a: U32, +b: U32, +c: U32, +d: U32) -> Sum:
  match same:
    case True{}:
      Sum{TFlat{a}, a, True{}}
    case False{}:
      Sum{TLeaf{a, b, c, d}, a, False{}}

def Tex.leaf(+a: U32, +b: U32, +c: U32, +d: U32) -> Sum:
  Tex.leaf.go((U32.is_eq(a, b) && U32.is_eq(b, c) && U32.is_eq(c, d)), a, b, c, d)

def Tex.join.go(same: Bool, +c: U32, t0: Tex, t1: Tex, t2: Tex, t3: Tex) -> Sum:
  match same:
    case True{}:
      Sum{TFlat{c}, c, True{}}
    case False{}:
      Sum{TNode{t0, t1, t2, t3}, c, False{}}

def Tex.join(s0: Sum, s1: Sum, s2: Sum, s3: Sum) -> Sum:
  Sum{t0, +c0, f0} = s0
  Sum{t1, +c1, f1} = s1
  Sum{t2, +c2, f2} = s2
  Sum{t3, c3, f3} = s3
  Tex.join.go((f0 && f1 && f2 && f3 && U32.is_eq(c0, c1) && U32.is_eq(c1, c2) && U32.is_eq(c2, c3)), c0, t0, t1, t2, t3)

def Tex.level(xs: List<Sum>, acc: List<Sum>) -> List<Sum>:
  match xs:
    case a <> b <> c <> d <> rest:
      Tex.level(rest, Tex.join(a, b, c, d) <> acc)
    case _:
      acc

def Tex.none(+c: U32) -> U32 & Tex:
  (1, TFlat{c})

def Tex.word(+b0: U32, +b1: U32, +b2: U32, +b3: U32) -> U32:
  (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216 : U32)

def Tex.bleafs(bytes: List<&2, U32>, acc: List<Sum>) -> List<Sum>:
  match bytes:
    case a0 <> a1 <> a2 <> a3 <> b0 <> b1 <> b2 <> b3 <> c0 <> c1 <> c2 <> c3 <> d0 <> d1 <> d2 <> d3 <> rest:
      Tex.bleafs(rest, Tex.leaf(Tex.word(a0, a1, a2, a3), Tex.word(b0, b1, b2, b3), Tex.word(c0, c1, c2, c3), Tex.word(d0, d1, d2, d3)) <> acc)
    case _:
      acc

def Tex.chunk() -> U32:
  16384

def Tex.firstS(xs: List<Sum>) -> Sum:
  match xs:
    case s <> _:
      s
    case _:
      Sum{TFlat{16777215}, 16777215, True{}}

def Tex.upS(k: Nat, xs: List<Sum>) -> Sum:
  match k:
    case 0n:
      Tex.firstS(xs)
    case 1n+j:
      Tex.upS(j, List.reverse(&1, Sum, Tex.level(xs, Nil{})))

def Tex.sub(+k: Nat, bytes: List<&2, U32>) -> Sum:
  Tex.upS(k, List.reverse(&1, Sum, Tex.bleafs(bytes, Nil{})))

def Tex.reads(k: Nat, +sub: Nat, +offset: U32, acc: List<Sum>, r: File & Got(List<&2, U32>)) -> IO(File & List<Sum>):
  match k:
    case 0n:
      (file, _) = r
      IO.pure(File & List<Sum>, (file, acc))
    case 1n+j:
      (file, res) = r
      match res:
        case Fail{_}:
          IO.pure(File & List<Sum>, (file, acc))
        case Done{bytes}:
          match bytes:
            case Nil{}:
              IO.pure(File & List<Sum>, (file, acc))
            case other:
              +next = (offset + Tex.chunk() : U32)
              do IO<File & List<Sum>>:
                r2 : File & Got(List<&2, U32>) <- File.read_at(file, next, Tex.chunk())
                Tex.reads(j, sub, next, Tex.sub(sub, other) <> acc, r2)

def Sum.tex(s: Sum) -> Tex:
  Sum{t, _, _} = s
  t

def Tex.fin(+d: Nat, fl: File & List<Sum>) -> IO(U32 & Tex):
  (file, subs) = fl
  do IO<U32 & Tex>:
    Unit <- File.close(file)
    IO.pure(U32 & Tex, (U32.shln(1, d), Sum.tex(Tex.upS(Nat.sub(d, Nat.min(d, 5n)), List.reverse(&1, Sum, subs)))))

def Tex.head(r: File & Got(List<&2, U32>), +flat: U32) -> IO(U32 & Tex):
  (file, res) = r
  match res:
    case Done{b0 <> b1 <> b2 <> b3 <> _}:
      +d = U32.to_nat(Tex.word(b0, b1, b2, b3))
      do IO<U32 & Tex>:
        r2 : File & Got(List<&2, U32>) <- File.read_at(file, 4, Tex.chunk())
        fl : File & List<Sum> <- Tex.reads(65536n, Nat.min(d, 5n), 4, Nil{}, r2)
        Tex.fin(d, fl)
    case _:
      do IO<U32 & Tex>:
        Unit <- File.close(file)
        IO.pure(U32 & Tex, Tex.none(flat))

def Tex.opened(r: Got(File), +flat: U32) -> IO(U32 & Tex):
  match r:
    case Done{f}:
      do IO<U32 & Tex>:
        h : File & Got(List<&2, U32>) <- File.read_at(f, 0, 4)
        Tex.head(h, flat)
    case Fail{_}:
      IO.pure(U32 & Tex, Tex.none(flat))

def Mats.fallback(r: Got(File), dir: String, kind: String, +flat: U32) -> IO(U32 & Tex):
  match r:
    case Done{f}:
      Tex.opened(Done{f}, flat)
    case Fail{_}:
      do IO<U32 & Tex>:
        r2 : Got(File) <- File.open(dir ++ "m0." ++ kind ++ ".tex", "r")
        Tex.opened(r2, flat)

def Mats.tex(has: Bool, +dir: String, +i: U32, +kind: String, +flat: U32) -> IO(U32 & Tex):
  match has:
    case False{}:
      IO.pure(U32 & Tex, Tex.none(flat))
    case True{}:
      do IO<U32 & Tex>:
        r : Got(File) <- File.open(dir ++ "m" ++ U32.show(i) ++ "." ++ kind ++ ".tex", "r")
        Mats.fallback(r, dir, kind, flat)

def Mats.cons(bp: U32 & Tex, mp: U32 & Tex, np: U32 & Tex, +metal: F32, +rough: F32, +ns: F32, +er: F32, +eg: F32, +eb: F32, acc: List<&2, Mats>) -> List<&2, Mats>:
  (pw, base) = bp
  (mpw, mr) = mp
  (npw, nrm) = np
  MtLeaf{pw, base, mpw, mr, npw, nrm, metal, rough, ns, er, eg, eb} <> acc

def Mats.load(flags: List<&2, U32>, +dir: String, acc: List<&2, Mats>) -> IO(List<&2, Mats>):
  match flags:
    case +fl <> me <> ro <> ns <> er <> eg <> eb <> rest:
      do IO<List<&2, Mats>>:
        b : U32 & Tex <- Mats.tex(U32.is_eq((fl .&. 1 : U32), 1), dir, (fl / 8 : U32), "base", 16777215)
        m : U32 & Tex <- Mats.tex(U32.is_eq((fl .&. 2 : U32), 2), dir, (fl / 8 : U32), "mr", 16777215)
        nm : U32 & Tex <- Mats.tex(U32.is_eq((fl .&. 4 : U32), 4), dir, (fl / 8 : U32), "normal", 8421631)
        Mats.load(rest, dir, Mats.cons(b, m, nm, Bits.f32(me), Bits.f32(ro), Bits.f32(ns), Bits.f32(er), Bits.f32(eg), Bits.f32(eb), acc))
    case _:
      IO.pure(List<&2, Mats>, acc)

def Mats.pad(k: Nat, acc: List<&2, Mats>) -> List<&2, Mats>:
  match k:
    case 0n:
      acc
    case 1n+j:
      Mats.pad(j, MtNone{} <> acc)

def Mats.tree(+xs: List<&2, Mats>) -> Mats:
  Pairs.up(~Mats, ~(a => b => MtNode{a, b}), ~(a => MtNode{a, MtNone{}}), ~MtNone{}, 8n, List.append(&2, Mats, xs, Mats.pad(Nat.sub(256n, List.length(&2, Mats, xs)), Nil{})))

def Em.of(flags: List<&2, U32>, acc: List<&2, Em>) -> List<&2, Em>:
  match flags:
    case _ <> _ <> _ <> _ <> +er <> +eg <> +eb <> rest:
      Em.of(rest, Em{Em.lum(Bits.f32(er), Bits.f32(eg), Bits.f32(eb)), Bits.f32(er), Bits.f32(eg), Bits.f32(eb)} <> acc)
    case _:
      acc

def Dir.cut(cs: List<&2, Char>, hit: Bool) -> List<&2, Char>:
  match cs hit:
    case rest True{}:
      '/' <> rest
    case Nil{} False{}:
      Nil{}
    case +c <> rest False{}:
      Dir.cut(rest, Char.is_eq(c, '/') || Char.is_eq(c, '\u{5c}'))

def Dir.of(path: String) -> String:
  String.from_list(List.reverse(&2, Char, Dir.cut(List.reverse(&2, Char, String.to_list(path)), False{})))

type Tris is Data:
  TNil{}
  TCons{+x0: F32, +y0: F32, +z0: F32, +ax: F32, +ay: F32, +az: F32, +bx: F32, +by: F32, +bz: F32,
    +n0x: F32, +n0y: F32, +n0z: F32, +n1x: F32, +n1y: F32, +n1z: F32, +n2x: F32, +n2y: F32, +n2z: F32,
    +u0: F32, +v0: F32, +u1: F32, +v1: F32, +u2: F32, +v2: F32, +tan: U32, +geo: U32,
    +col: U32, +metal: F32, +rough: F32, +le: F32, next: Tris}

type Bvh is Data:
  BLeaf{ts: Tris}
  BNode{+lx0: F32, +ly0: F32, +lz0: F32, +lx1: F32, +ly1: F32, +lz1: F32, +rx0: F32, +ry0: F32, +rz0: F32, +rx1: F32, +ry1: F32, +rz1: F32, l: Bvh, r: Bvh}

type Built is Data:
  Built{b: Bvh, +x0: F32, +y0: F32, +z0: F32, +x1: F32, +y1: F32, +z1: F32, +cost: F32}

def Tan.q(+x: F32) -> U32:
  F32.to_u32((F32.clamp(x, (0.0 - 1.0 : F32), 1.0) * 511.5 + 511.5 : F32))

def Tan.vec(+x: F32, +y: F32, +z: F32) -> U32:
  +il = (1.0 / F32.max(0.000000001, F32.sqrt((x * x + y * y + z * z : F32))) : F32)
  (Tan.q((x * il : F32)) * 1048576 + Tan.q((y * il : F32)) * 1024 + Tan.q((z * il : F32)) : U32)

def Tan.pack(+ax: F32, +ay: F32, +az: F32, +bx: F32, +by: F32, +bz: F32, +du1: F32, +dv1: F32, +du2: F32, +dv2: F32) -> U32:
  +det = (du1 * dv2 - du2 * dv1 : F32)
  +r = sel(~F32, (F32.max(det, (0.0 - det : F32)) < 0.000000001 : F32), 0.0, (1.0 / det : F32))
  +tx = ((ax * dv2 - bx * dv1) * r : F32)
  +ty = ((ay * dv2 - by * dv1) * r : F32)
  +tz = ((az * dv2 - bz * dv1) * r : F32)
  +il = (1.0 / F32.max(0.000000001, F32.sqrt((tx * tx + ty * ty + tz * tz : F32))) : F32)
  +ux = (tx * il : F32)
  +uy = (ty * il : F32)
  +uz = (tz * il : F32)
  +nx = (ay * bz - az * by : F32)
  +ny = (az * bx - ax * bz : F32)
  +nz = (ax * by - ay * bx : F32)
  +w = ((ny * uz - nz * uy) * (bx * du1 - ax * du2) + (nz * ux - nx * uz) * (by * du1 - ay * du2) + (nx * uy - ny * ux) * (bz * du1 - az * du2) : F32)
  (Tan.q(ux) * 1048576 + Tan.q(uy) * 1024 + Tan.q(uz) + sel(~U32, (w < 0.0 : F32), 0, 1073741824) : U32)

def Tri.make(x0: F32, y0: F32, z0: F32, +ax: F32, +ay: F32, +az: F32, +bx: F32, +by: F32, +bz: F32, n0x: F32, n0y: F32, n0z: F32, n1x: F32, n1y: F32, n1z: F32, n2x: F32, n2y: F32, n2z: F32, +u0: F32, +v0: F32, +u1: F32, +v1: F32, +u2: F32, +v2: F32, col: U32, metal: F32, rough: F32, le: F32, acc: Tris) -> Tris:
  TCons{x0, y0, z0, ax, ay, az, bx, by, bz, n0x, n0y, n0z, n1x, n1y, n1z, n2x, n2y, n2z, u0, v0, u1, v1, u2, v2, Tan.pack(ax, ay, az, bx, by, bz, (u1 - u0 : F32), (v1 - v0 : F32), (u2 - u0 : F32), (v2 - v0 : F32)), Tan.vec((ay * bz - az * by : F32), (az * bx - ax * bz : F32), (ax * by - ay * bx : F32)), col, metal, rough, le, acc}

def Tri.of(a: V, b: V, c: V, +m: Mat, acc: Tris) -> Tris:
  V{+x0, +y0, +z0, n0x, n0y, n0z, u0, v0} = a
  V{x1, y1, z1, n1x, n1y, n1z, u1, v1} = b
  V{x2, y2, z2, n2x, n2y, n2z, u2, v2} = c
  Mat{col, metal, rough, le} = m
  Tri.make(x0, y0, z0, (x1 - x0 : F32), (y1 - y0 : F32), (z1 - z0 : F32), (x2 - x0 : F32), (y2 - y0 : F32), (z2 - z0 : F32), n0x, n0y, n0z, n1x, n1y, n1z, n2x, n2y, n2z, u0, v0, u1, v1, u2, v2, col, metal, rough, le, acc)

def Tri.c(p: Array<F32> & V, q: V, w: V, +f: Fit, +m: Mat, acc: Tris) -> Array<F32> & Tris:
  match p:
    case (a, v):
      (a, Tri.of(V.fit(v, f), q, w, m, acc))

def Tri.b(p: Array<F32> & V, +k: U32, q: V, +f: Fit, +m: Mat, acc: Tris) -> Array<F32> & Tris:
  match p:
    case (a, v):
      Tri.c(V.at(a, k), q, V.fit(v, f), f, m, acc)

def Tri.a(p: Array<F32> & V, +j: U32, +k: U32, +f: Fit, +m: Mat, acc: Tris) -> Array<F32> & Tris:
  match p:
    case (a, v):
      Tri.b(V.at(a, j), k, V.fit(v, f), f, m, acc)

def Tri.add(p: Array<F32> & Tris, +i: U32, +j: U32, +k: U32, +f: Fit, +m: Mat) -> Array<F32> & Tris:
  match p:
    case (a, acc):
      Tri.a(V.at(a, i), j, k, f, m, acc)

def Load.keep(keep: Bool, +i: U32, +j: U32, +l: U32, got: List<&2, U32>) -> List<&2, U32>:
  match keep:
    case True{}:
      i <> j <> l <> got
    case False{}:
      got

def Load.ids(n: Nat, ws: List<&2, U32>, p: Array<F32> & Tris, +f: Fit, +m: Mat, +keep: Bool, got: List<&2, U32>) -> Tris & (List<&2, U32> & List<&2, U32>):
  match n ws:
    case 0n rest:
      (a, acc) = p
      (acc, (rest, got))
    case 1n+k +i <> +j <> +l <> rest:
      Load.ids(k, rest, Tri.add(p, i, j, l, f, m), f, m, keep, Load.keep(keep, i, j, l, got))
    case _ _:
      (a, acc) = p
      (acc, (Nil{}, got))

type Step is Data:
  Step{ts: Tris, ws: List<&2, U32>, prim: Prim}

def Load.close(r: Tris & (List<&2, U32> & List<&2, U32>), +m: Mat, +skin: U32, +k: Nat, rv: Tree4<Vert>) -> Step:
  (ts, wg) = r
  (ws, got) = wg
  Step{ts, ws, Prim{m, skin, k, rv, got}}

def Load.faces(n: Nat, avt: Array<F32> & (List<&2, U32> & Tree4<Vert>), +f: Fit, +m: Mat, +keep: Bool, +skin: U32, +k: Nat, acc: Tris) -> Step:
  (a, wt) = avt
  (ws, rv) = wt
  Load.close(Load.ids(n, ws, (a, acc), f, m, keep, Nil{}), m, skin, k, rv)

def Load.prim(+vc: U32, +tc: U32, +st: U32, ws: List<&2, U32>, +f: Fit, +m: Mat, +keep: Bool, +skin: U32, acc: Tris) -> Step:
  +k = Tree4.fit(vc)
  Load.faces(U32.to_nat(tc), Load.verts(U32.to_nat(vc), ws, U32.to_nat((st - 12 : U32)), Array.new(F32, Array.depth(32n, ((8 * vc : U32) <= 1 : U32), (8 * vc : U32), 1, 0n), 0.0), 0, keep, U32.is_eq(st, 17), k, T4Nil{}), f, m, keep, skin, k, acc)

type Loaded is Data:
  Loaded{ts: Tris, +n: U32, prims: List<&2, Prim>, rest: List<&2, U32>}

def Load.kept(keep: Bool, pr: Prim, ps: List<&2, Prim>) -> List<&2, Prim>:
  match keep:
    case True{}:
      pr <> ps
    case False{}:
      ps

@unsafe
def Load.more(pc: Nat, r: Step, +f: Fit, +n: U32, +pi: U32, +keep: Bool, ps: List<&2, Prim>) -> Loaded:
  Step{acc, ws, pr} = r
  Load.prims(pc, ws, f, acc, n, pi, keep, Load.kept(keep, pr, ps))

def Load.prims(pc: Nat, ws: List<&2, U32>, +f: Fit, acc: Tris, +n: U32, +pi: U32, +keep: Bool, ps: List<&2, Prim>) -> Loaded:
  match pc ws:
    case 0n rest:
      Loaded{acc, n, List.reverse(&2, Prim, ps), rest}
    case 1n+p vc <> +tc <> sk <> st <> r <> g <> b <> a <> me <> ro <> fl <> ns <> er <> eg <> eb <> x0 <> y0 <> z0 <> x1 <> y1 <> z1 <> rest:
      Load.more(p, Load.prim(vc, tc, st, rest, f, Mat{(pack(Bits.f32(r), Bits.f32(g), Bits.f32(b)) .|. (pi * 16777216 : U32) : U32), Bits.f32(me), Bits.f32(ro), Em.lum(Bits.f32(er), Bits.f32(eg), Bits.f32(eb))}, keep, sk, acc), f, (n + tc : U32), (pi + 1 : U32), keep, ps)
    case _ _:
      Loaded{acc, n, List.reverse(&2, Prim, ps), Nil{}}

def Tris.box(+ts: Tris, acc: Box) -> Box:
  match ts:
    case TNil{}:
      acc
    case TCons{x0, y0, z0, ax, ay, az, bx, by, bz, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, next}:
      Tris.box(next, Box.add(Box.add(Box.add(acc, x0, y0, z0), (x0 + ax : F32), (y0 + ay : F32), (z0 + az : F32)), (x0 + bx : F32), (y0 + by : F32), (z0 + bz : F32)))

def Tris.cen(+ts: Tris, acc: Box) -> Box:
  match ts:
    case TNil{}:
      acc
    case TCons{x0, y0, z0, ax, ay, az, bx, by, bz, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, next}:
      Tris.cen(next, Box.add(acc, (x0 + (ax + bx) / 3.0 : F32), (y0 + (ay + by) / 3.0 : F32), (z0 + (az + bz) / 3.0 : F32)))

type Part is Data:
  Part{l: Tris, +nl: U32, r: Tris, +nr: U32}

def Tris.on(+axis: U32, +cx: F32, +cy: F32, +cz: F32) -> F32:
  sel(~F32, U32.is_eq(axis, 0), cx, sel(~F32, U32.is_eq(axis, 1), cy, cz))

def Part.put(left: Bool, +x0: F32, +y0: F32, +z0: F32, +ax: F32, +ay: F32, +az: F32, +bx: F32, +by: F32, +bz: F32, +n0x: F32, +n0y: F32, +n0z: F32, +n1x: F32, +n1y: F32, +n1z: F32, +n2x: F32, +n2y: F32, +n2z: F32, +u0: F32, +v0: F32, +u1: F32, +v1: F32, +u2: F32, +v2: F32, +tan: U32, +geo: U32, +col: U32, +metal: F32, +rough: F32, +le: F32, p: Part) -> Part:
  match left:
    case True{}:
      Part{l, nl, r, nr} = p
      Part{TCons{x0, y0, z0, ax, ay, az, bx, by, bz, n0x, n0y, n0z, n1x, n1y, n1z, n2x, n2y, n2z, u0, v0, u1, v1, u2, v2, tan, geo, col, metal, rough, le, l}, (nl + 1 : U32), r, nr}
    case False{}:
      Part{l, nl, r, nr} = p
      Part{l, nl, TCons{x0, y0, z0, ax, ay, az, bx, by, bz, n0x, n0y, n0z, n1x, n1y, n1z, n2x, n2y, n2z, u0, v0, u1, v1, u2, v2, tan, geo, col, metal, rough, le, r}, (nr + 1 : U32)}

def Tris.part(ts: Tris, +axis: U32, +mid: F32, p: Part) -> Part:
  match ts:
    case TNil{}:
      p
    case TCons{x0, y0, z0, ax, ay, az, bx, by, bz, n0x, n0y, n0z, n1x, n1y, n1z, n2x, n2y, n2z, u0, v0, u1, v1, u2, v2, tan, geo, col, metal, rough, le, next}:
      Tris.part(next, axis, mid, Part.put((Tris.on(axis, (x0 + (ax + bx) / 3.0 : F32), (y0 + (ay + by) / 3.0 : F32), (z0 + (az + bz) / 3.0 : F32)) < mid : F32), x0, y0, z0, ax, ay, az, bx, by, bz, n0x, n0y, n0z, n1x, n1y, n1z, n2x, n2y, n2z, u0, v0, u1, v1, u2, v2, tan, geo, col, metal, rough, le, p))

def Tris.count(+ts: Tris, +n: U32) -> U32:
  match ts:
    case TNil{}:
      n
    case TCons{_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, next}:
      Tris.count(next, (n + 1 : U32))

def Tris.halve(n: Nat, ts: Tris, p: Part) -> Part:
  match n ts:
    case 0n +rest:
      Part{l, nl, r, nr} = p
      Part{l, nl, rest, Tris.count(rest, 0)}
    case 1n+m TCons{x0, y0, z0, ax, ay, az, bx, by, bz, n0x, n0y, n0z, n1x, n1y, n1z, n2x, n2y, n2z, u0, v0, u1, v1, u2, v2, tan, geo, col, metal, rough, le, next}:
      Tris.halve(m, next, Part.put(True{}, x0, y0, z0, ax, ay, az, bx, by, bz, n0x, n0y, n0z, n1x, n1y, n1z, n2x, n2y, n2z, u0, v0, u1, v1, u2, v2, tan, geo, col, metal, rough, le, p))
    case 1n+m TNil{}:
      p

def Tris.app(a: Tris, b: Tris) -> Tris:
  match a:
    case TNil{}:
      b
    case TCons{x0, y0, z0, ax, ay, az, bx, by, bz, n0x, n0y, n0z, n1x, n1y, n1z, n2x, n2y, n2z, u0, v0, u1, v1, u2, v2, tan, geo, col, metal, rough, le, next}:
      TCons{x0, y0, z0, ax, ay, az, bx, by, bz, n0x, n0y, n0z, n1x, n1y, n1z, n2x, n2y, n2z, u0, v0, u1, v1, u2, v2, tan, geo, col, metal, rough, le, Tris.app(next, b)}

def Bvh.leaf2(ts: Tris, b: Box, +n: U32) -> Built:
  Box{+x0, +y0, +z0, +x1, +y1, +z1} = b
  Built{BLeaf{ts}, x0, y0, z0, x1, y1, z1, (Box.area(x0, y0, z0, x1, y1, z1) * U32.to_f32(n) : F32)}

def Bvh.leaf(+ts: Tris) -> Built:
  Bvh.leaf2(ts, Tris.box(ts, Box.empty()), Tris.count(ts, 0))

def Bvh.join(pa: Built, pb: Built) -> Built:
  Built{a, +ax0, +ay0, +az0, +ax1, +ay1, +az1, ca} = pa
  Built{b, +bx0, +by0, +bz0, +bx1, +by1, +bz1, cb} = pb
  +x0 = F32.min(ax0, bx0)
  +y0 = F32.min(ay0, by0)
  +z0 = F32.min(az0, bz0)
  +x1 = F32.max(ax1, bx1)
  +y1 = F32.max(ay1, by1)
  +z1 = F32.max(az1, bz1)
  Built{BNode{ax0, ay0, az0, ax1, ay1, az1, bx0, by0, bz0, bx1, by1, bz1, a, b}, x0, y0, z0, x1, y1, z1, (Box.area(x0, y0, z0, x1, y1, z1) + ca + cb : F32)}

def Box.axis(b: Box) -> U32:
  Box{x0, y0, z0, x1, y1, z1} = b
  +dx = (x1 - x0 : F32)
  +dy = (y1 - y0 : F32)
  +dz = (z1 - z0 : F32)
  sel(~U32, ((dx >= dy) && (dx >= dz) : F32), 0, sel(~U32, (dy >= dz : F32), 1, 2))

def Box.mid(b: Box, +axis: U32) -> F32:
  Box{x0, y0, z0, x1, y1, z1} = b
  ((Tris.on(axis, x0, y0, z0) + Tris.on(axis, x1, y1, z1)) * 0.5 : F32)

type Bin is Data:
  Bin{+x0: F32, +y0: F32, +z0: F32, +x1: F32, +y1: F32, +z1: F32, +n: F32}

type Cand is Data:
  Cand{+cost: F32, +axis: U32, +mid: F32}

def Sah.empty(+i: U32) -> F32:
  +r = (i % 7 : U32)
  sel(~F32, (r < 3 : U32), 1000000000.0, sel(~F32, (r < 6 : U32), (0.0 - 1000000000.0 : F32), 0.0))

def Sah.init(k: Nat, a: Array<F32>, +i: U32) -> Array<F32>:
  match k:
    case 0n:
      a
    case 1n+j:
      Sah.init(j, Array.set(F32, a, i, Sah.empty(i)), (i + 1 : U32))

def Sah.min2(r: Array<F32> & F32, +i: U32, +v: F32) -> Array<F32>:
  match r:
    case (a, old):
      Array.set(F32, a, i, F32.min(old, v))

def Sah.min(a: Array<F32>, +i: U32, +v: F32) -> Array<F32>:
  Sah.min2(Array.get(F32, a, i), i, v)

def Sah.max2(r: Array<F32> & F32, +i: U32, +v: F32) -> Array<F32>:
  match r:
    case (a, old):
      Array.set(F32, a, i, F32.max(old, v))

def Sah.max(a: Array<F32>, +i: U32, +v: F32) -> Array<F32>:
  Sah.max2(Array.get(F32, a, i), i, v)

def Sah.inc2(r: Array<F32> & F32, +i: U32) -> Array<F32>:
  match r:
    case (a, old):
      Array.set(F32, a, i, (old + 1.0 : F32))

def Sah.inc(a: Array<F32>, +i: U32) -> Array<F32>:
  Sah.inc2(Array.get(F32, a, i), i)

def Sah.put(a: Array<F32>, +b: U32, +x0: F32, +y0: F32, +z0: F32, +x1: F32, +y1: F32, +z1: F32) -> Array<F32>:
  Sah.inc(Sah.max(Sah.max(Sah.max(Sah.min(Sah.min(Sah.min(a, b, x0), (b + 1 : U32), y0), (b + 2 : U32), z0), (b + 3 : U32), x1), (b + 4 : U32), y1), (b + 5 : U32), z1), (b + 6 : U32))

def Sah.slot(+c: F32, +lo: F32, +inv: F32) -> U32:
  F32.to_u32(F32.clamp(((c - lo) * inv : F32), 0.0, 7.0))

def Sah.inv(+lo: F32, +hi: F32) -> F32:
  sel(~F32, (hi - lo <= 0.000001 : F32), 0.0, (8.0 / (hi - lo) : F32))

def Sah.walk(+ts: Tris, a: Array<F32>, +lx: F32, +ix: F32, +ly: F32, +iy: F32, +lz: F32, +iz: F32) -> Array<F32>:
  match ts:
    case TNil{}:
      a
    case TCons{x0, y0, z0, ax, ay, az, bx, by, bz, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, next}:
      +x1 = (x0 + ax : F32)
      +y1 = (y0 + ay : F32)
      +z1 = (z0 + az : F32)
      +x2 = (x0 + bx : F32)
      +y2 = (y0 + by : F32)
      +z2 = (z0 + bz : F32)
      +tx0 = F32.min(x0, F32.min(x1, x2))
      +ty0 = F32.min(y0, F32.min(y1, y2))
      +tz0 = F32.min(z0, F32.min(z1, z2))
      +tx1 = F32.max(x0, F32.max(x1, x2))
      +ty1 = F32.max(y0, F32.max(y1, y2))
      +tz1 = F32.max(z0, F32.max(z1, z2))
      Sah.walk(next, Sah.put(Sah.put(Sah.put(a, (Sah.slot((x0 + (ax + bx) / 3.0 : F32), lx, ix) * 7 : U32), tx0, ty0, tz0, tx1, ty1, tz1), ((8 + Sah.slot((y0 + (ay + by) / 3.0 : F32), ly, iy)) * 7 : U32), tx0, ty0, tz0, tx1, ty1, tz1), ((16 + Sah.slot((z0 + (az + bz) / 3.0 : F32), lz, iz)) * 7 : U32), tx0, ty0, tz0, tx1, ty1, tz1), lx, ix, ly, iy, lz, iz)

def Sah.r7(r: Array<F32> & F32, +x0: F32, +y0: F32, +z0: F32, +x1: F32, +y1: F32, +z1: F32) -> Array<F32> & Bin:
  match r:
    case (a, n):
      (a, Bin{x0, y0, z0, x1, y1, z1, n})

def Sah.r6(r: Array<F32> & F32, +b: U32, +x0: F32, +y0: F32, +z0: F32, +x1: F32, +y1: F32) -> Array<F32> & Bin:
  match r:
    case (a, z1):
      Sah.r7(Array.get(F32, a, (b + 6 : U32)), x0, y0, z0, x1, y1, z1)

def Sah.r5(r: Array<F32> & F32, +b: U32, +x0: F32, +y0: F32, +z0: F32, +x1: F32) -> Array<F32> & Bin:
  match r:
    case (a, y1):
      Sah.r6(Array.get(F32, a, (b + 5 : U32)), b, x0, y0, z0, x1, y1)

def Sah.r4(r: Array<F32> & F32, +b: U32, +x0: F32, +y0: F32, +z0: F32) -> Array<F32> & Bin:
  match r:
    case (a, x1):
      Sah.r5(Array.get(F32, a, (b + 4 : U32)), b, x0, y0, z0, x1)

def Sah.r3(r: Array<F32> & F32, +b: U32, +x0: F32, +y0: F32) -> Array<F32> & Bin:
  match r:
    case (a, z0):
      Sah.r4(Array.get(F32, a, (b + 3 : U32)), b, x0, y0, z0)

def Sah.r2(r: Array<F32> & F32, +b: U32, +x0: F32) -> Array<F32> & Bin:
  match r:
    case (a, y0):
      Sah.r3(Array.get(F32, a, (b + 2 : U32)), b, x0, y0)

def Sah.r1(r: Array<F32> & F32, +b: U32) -> Array<F32> & Bin:
  match r:
    case (a, x0):
      Sah.r2(Array.get(F32, a, (b + 1 : U32)), b, x0)

def Sah.read(a: Array<F32>, +b: U32) -> Array<F32> & Bin:
  Sah.r1(Array.get(F32, a, b), b)

def Sah.rd2(q: Array<F32> & Bin, acc: List<&2, Bin>) -> Array<F32> & List<&2, Bin>:
  match q:
    case (a, bin):
      (a, bin <> acc)

def Sah.rd(r: Array<F32> & List<&2, Bin>, +b: U32) -> Array<F32> & List<&2, Bin>:
  match r:
    case (a, acc):
      Sah.rd2(Sah.read(a, b), acc)

def Sah.axis(k: Nat, r: Array<F32> & List<&2, Bin>, +base: U32, +i: U32) -> Array<F32> & List<&2, Bin>:
  match k:
    case 0n:
      r
    case 1n+j:
      Sah.axis(j, Sah.rd(r, (base + i * 7 : U32)), base, (i - 1 : U32))

def Bin.none() -> Bin:
  Bin{1000000000.0, 1000000000.0, 1000000000.0, (0.0 - 1000000000.0 : F32), (0.0 - 1000000000.0 : F32), (0.0 - 1000000000.0 : F32), 0.0}

def Bin.union(a: Bin, b: Bin) -> Bin:
  Bin{ax0, ay0, az0, ax1, ay1, az1, an} = a
  Bin{bx0, by0, bz0, bx1, by1, bz1, bn} = b
  Bin{F32.min(ax0, bx0), F32.min(ay0, by0), F32.min(az0, bz0), F32.max(ax1, bx1), F32.max(ay1, by1), F32.max(az1, bz1), (an + bn : F32)}

def Sah.prefix(bins: List<&2, Bin>, acc: Bin, out: List<&2, Bin>) -> List<&2, Bin>:
  match bins:
    case Nil{}:
      out
    case b <> rest:
      +u = Bin.union(acc, b)
      Sah.prefix(rest, u, u <> out)

def Bin.cost(b: Bin) -> F32:
  Bin{x0, y0, z0, x1, y1, z1, +n} = b
  sel(~F32, (n < 0.5 : F32), 1000000000000.0, (Box.area(x0, y0, z0, x1, y1, z1) * n : F32))

def Cand.min(a: Cand, b: Cand) -> Cand:
  Cand{+ca, aa, ma} = a
  Cand{+cb, ab, mb} = b
  sel(~Cand, (ca < cb : F32), Cand{ca, aa, ma}, Cand{cb, ab, mb})

def Sah.scan(ls: List<&2, Bin>, rs: List<&2, Bin>, +k: U32, +axis: U32, +lo: F32, +w: F32, best: Cand) -> Cand:
  match ls rs:
    case l <> ls2 r <> rs2:
      Sah.scan(ls2, rs2, (k + 1 : U32), axis, lo, w, Cand.min(Cand{(Bin.cost(l) + Bin.cost(r) : F32), axis, (lo + U32.to_f32((k + 1 : U32)) * w : F32)}, best))
    case _ _:
      best

def Sah.eval(+bins: List<&2, Bin>, +axis: U32, +lo: F32, +hi: F32) -> Cand:
  Sah.scan(List.reverse(&2, Bin, Sah.prefix(bins, Bin.none(), Nil{})), List.drop(&2, Bin, Sah.prefix(List.reverse(&2, Bin, bins), Bin.none(), Nil{}), 1n), 0, axis, lo, ((hi - lo) / 8.0 : F32), Cand{1000000000000.0, axis, lo})

def Sah.one(r: Array<F32> & List<&2, Bin>, by: List<&2, Bin>, bz: List<&2, Bin>, c: Box) -> Cand:
  match r:
    case (a, bx):
      Box{x0, y0, z0, x1, y1, z1} = c
      Cand.min(Sah.eval(bx, 0, x0, x1), Cand.min(Sah.eval(by, 1, y0, y1), Sah.eval(bz, 2, z0, z1)))

def Sah.two(r: Array<F32> & List<&2, Bin>, bz: List<&2, Bin>, c: Box) -> Cand:
  match r:
    case (a, by):
      Sah.one(Sah.axis(8n, (a, Nil{}), 0, 7), by, bz, c)

def Sah.three(r: Array<F32> & List<&2, Bin>, c: Box) -> Cand:
  match r:
    case (a, bz):
      Sah.two(Sah.axis(8n, (a, Nil{}), 56, 7), bz, c)

def Sah.choose(+ts: Tris, +c: Box) -> Cand:
  Box{cx0, cy0, cz0, cx1, cy1, cz1} = c
  Sah.three(Sah.axis(8n, (Sah.walk(ts, Sah.init(168n, Array.new(F32, 8n, 0.0), 0), cx0, Sah.inv(cx0, cx1), cy0, Sah.inv(cy0, cy1), cz0, Sah.inv(cz0, cz1)), Nil{}), 112, 7), c)

@unsafe
def Bvh.build(fuel: Nat, ts: Tris, +n: U32) -> Built:
  match fuel:
    case 0n:
      Bvh.leaf(ts)
    case 1n+f:
      Bvh.split(f, ts, n, (n <= 4 : U32))

def Bvh.node(+f: Nat, l: Tris, +nl: U32, r: Tris, +nr: U32) -> Built:
  a b = Bvh.build(f, l, nl) Bvh.build(f, r, nr)
  Bvh.join(a, b)

def Bvh.halved(f: Nat, p: Part) -> Built:
  Part{l, +nl, r, +nr} = p
  Bvh.node(f, l, nl, r, nr)

def Bvh.ok(f: Nat, good: Bool, l: Tris, +nl: U32, r: Tris, +nr: U32) -> Built:
  match good:
    case True{}:
      Bvh.node(f, l, nl, r, nr)
    case False{}:
      Bvh.halved(f, Tris.halve(U32.to_nat(((nl + nr) / 2 : U32)), Tris.app(l, r), Part{TNil{}, 0, TNil{}, 0}))

def Bvh.parted(f: Nat, p: Part, +n: U32) -> Built:
  Part{l, +nl, r, +nr} = p
  Bvh.ok(f, ((nl >= 1) && (nr >= 1) : U32), l, nl, r, nr)

def Bvh.cand(f: Nat, ts: Tris, +n: U32, cand: Cand) -> Built:
  Cand{_, +axis, +mid} = cand
  Bvh.parted(f, Tris.part(ts, axis, mid, Part{TNil{}, 0, TNil{}, 0}), n)

def Bvh.split(f: Nat, +ts: Tris, +n: U32, small: Bool) -> Built:
  match small:
    case True{}:
      Bvh.leaf(ts)
    case False{}:
      +c = Tris.cen(ts, Box.empty())
      Bvh.cand(f, ts, n, Sah.choose(ts, c))

def Bvh.of(b: Built) -> Bvh:
  Built{t, _, _, _, _, _, _, _} = b
  t

def Bvh.levels() -> Nat:
  29n

def Tri.moved(p: Vec3, e: Vec3, f: Vec3, n0: Vec3, n1: Vec3, n2: Vec3, +u0: F32, +v0: F32, +u1: F32, +v1: F32, +u2: F32, +v2: F32, +col: U32, +metal: F32, +rough: F32, +le: F32, acc: Tris) -> Tris:
  Vec3{x0, y0, z0} = p
  Vec3{ax, ay, az} = e
  Vec3{bx, by, bz} = f
  Vec3{n0x, n0y, n0z} = n0
  Vec3{n1x, n1y, n1z} = n1
  Vec3{n2x, n2y, n2z} = n2
  Tri.make(x0, y0, z0, ax, ay, az, bx, by, bz, n0x, n0y, n0z, n1x, n1y, n1z, n2x, n2y, n2z, u0, v0, u1, v1, u2, v2, col, metal, rough, le, acc)

def Tris.xf(+m: Mat4, +base: U32, ts: Tris, acc: Tris) -> Tris:
  match ts:
    case TNil{}:
      acc
    case TCons{x0, y0, z0, ax, ay, az, bx, by, bz, n0x, n0y, n0z, n1x, n1y, n1z, n2x, n2y, n2z, u0, v0, u1, v1, u2, v2, _, _, col, metal, rough, le, next}:
      Tris.xf(m, base, next, Tri.moved(Mat4.transform_point(m, Vec3{x0, y0, z0}), Mat4.transform_dir(m, Vec3{ax, ay, az}), Mat4.transform_dir(m, Vec3{bx, by, bz}), Vec3.normalize(Mat4.transform_dir(m, Vec3{n0x, n0y, n0z})), Vec3.normalize(Mat4.transform_dir(m, Vec3{n1x, n1y, n1z})), Vec3.normalize(Mat4.transform_dir(m, Vec3{n2x, n2y, n2z})), u0, v0, u1, v1, u2, v2, (col + base * 16777216 : U32), metal, rough, le, acc))

type Hit is Data:
  Hit{+t: F32, +nx: F32, +ny: F32, +nz: F32, +col: U32, +uv: U32, +tan: U32, +geo: U32, +le: F32}

def Ray.nz(+v: F32) -> F32:
  sel(~F32, (F32.max(v, (0.0 - v : F32)) < 0.000001 : F32), 0.000001, v)

def Slab.enter(+x0: F32, +y0: F32, +z0: F32, +x1: F32, +y1: F32, +z1: F32, +ox: F32, +oy: F32, +oz: F32, +ix: F32, +iy: F32, +iz: F32, +bt: F32) -> F32:
  +tx0 = ((x0 - ox) * ix : F32)
  +tx1 = ((x1 - ox) * ix : F32)
  +ty0 = ((y0 - oy) * iy : F32)
  +ty1 = ((y1 - oy) * iy : F32)
  +tz0 = ((z0 - oz) * iz : F32)
  +tz1 = ((z1 - oz) * iz : F32)
  +en = F32.max(F32.max(F32.min(tx0, tx1), F32.min(ty0, ty1)), F32.max(F32.min(tz0, tz1), 0.0))
  +ex = F32.min(F32.min(F32.max(tx0, tx1), F32.max(ty0, ty1)), F32.min(F32.max(tz0, tz1), bt))
  sel(~F32, (en <= ex : F32), en, 1000000000.0)

def Tri.tok(ok: Bool, +tt: F32, +ad: F32, +bt: F32) -> F32:
  match ok:
    case True{}:
      (tt / ad : F32)
    case False{}:
      bt

def Leaf.pickn(same: Bool, +a: F32, +b: F32, +c: F32, +u: F32, +v: F32, +ad: F32, +old: F32) -> F32:
  match same:
    case False{}:
      old
    case True{}:
      (((ad - u - v) * a + u * b + v * c) / ad : F32)

def Leaf.picku(same: Bool, +u0: F32, +v0: F32, +u1: F32, +v1: F32, +u2: F32, +v2: F32, +u: F32, +v: F32, +ad: F32, +old: U32) -> U32:
  match same:
    case False{}:
      old
    case True{}:
      +iu = (u / ad : F32)
      +iv = (v / ad : F32)
      +w = (1.0 - iu - iv : F32)
      +tu = (w * u0 + iu * u1 + iv * u2 : F32)
      +tv = (w * v0 + iu * v1 + iv * v2 : F32)
      (F32.to_u32(((tu - F32.floor(tu)) * 65535.0 : F32)) * 65536 + F32.to_u32(((tv - F32.floor(tv)) * 65535.0 : F32)) : U32)

def Walk.log2(+x: U32) -> U32:
  (sel(~U32, U32.is_eq((x .&. 4294901760 : U32), 0), 0, 16)
    + sel(~U32, U32.is_eq((x .&. 4278255360 : U32), 0), 0, 8)
    + sel(~U32, U32.is_eq((x .&. 4042322160 : U32), 0), 0, 4)
    + sel(~U32, U32.is_eq((x .&. 3435973836 : U32), 0), 0, 2)
    + sel(~U32, U32.is_eq((x .&. 2863311530 : U32), 0), 0, 1) : U32)

def Walk.go(fuel: Nat, stop: Bool, lf: Bool, adv: Bool, at: Bool, gr: Bool, pb: Bool, sw: Bool, e1: Bool, b: Bool, hv: Bool, +root: Bvh, cur: Bvh, tl: Tris, s1: Bvh, s2: Bvh, s3: Bvh, s4: Bvh, s5: Bvh, s6: Bvh, cr: Bvh, +k: U32, +rest: U32, +path: U32, +pw: U32, +d: U32, +todo: U32, +v: U32, +any: Bool, +ox: F32, +oy: F32, +oz: F32, +dx: F32, +dy: F32, +dz: F32, +ix: F32, +iy: F32, +iz: F32, +bt: F32, +bnx: F32, +bny: F32, +bnz: F32, +bc: U32, +buv: U32, +btn: U32, +bge: U32, +ble: F32) -> Hit:
  match fuel stop lf adv at gr pb sw e1 b hv cur tl:
    case 0n _ _ _ _ _ _ _ _ _ _ _ _:
      Hit{bt, bnx, bny, bnz, bc, buv, btn, bge, ble}
    case _ True{} _ _ _ _ _ _ _ _ _ _ _:
      Hit{bt, bnx, bny, bnz, bc, buv, btn, bge, ble}
    case 1n+f False{} True{} _ _ _ _ _ _ _ _ _ TCons{x0, y0, z0, ax, ay, az, bx, by, bz, n0x, n0y, n0z, n1x, n1y, n1z, n2x, n2y, n2z, u0, v0, u1, v1, u2, v2, tan, geo, col, _, _, le, next}:
      +px = (dy * bz - dz * by : F32)
      +py = (dz * bx - dx * bz : F32)
      +pz = (dx * by - dy * bx : F32)
      +det = (ax * px + ay * py + az * pz : F32)
      +sg = sel(~F32, (det < 0.0 : F32), (0.0 - 1.0 : F32), 1.0)
      +ad = (det * sg : F32)
      +wx = (ox - x0 : F32)
      +wy = (oy - y0 : F32)
      +wz = (oz - z0 : F32)
      +fu = (sg * (wx * px + wy * py + wz * pz) : F32)
      +qx = (wy * az - wz * ay : F32)
      +qy = (wz * ax - wx * az : F32)
      +qz = (wx * ay - wy * ax : F32)
      +fv = (sg * (dx * qx + dy * qy + dz * qz) : F32)
      +ft = (sg * (bx * qx + by * qy + bz * qz) : F32)
      +tt = Tri.tok(((fu >= 0.0) && (fv >= 0.0) && (fu + fv <= ad) && (ft > 0.0001 * ad) && (ft < bt * ad) : F32), ft, ad, bt)
      +better = (tt < bt : F32)
      Walk.go(f, (any && better), True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, root, root, next, s1, s2, s3, s4, s5, s6, cr, k, rest, path, pw, d, todo, v, any, ox, oy, oz, dx, dy, dz, ix, iy, iz, tt, Leaf.pickn(better, n0x, n1x, n2x, fu, fv, ad, bnx), Leaf.pickn(better, n0y, n1y, n2y, fu, fv, ad, bny), Leaf.pickn(better, n0z, n1z, n2z, fu, fv, ad, bnz), sel(~U32, better, col, bc), Leaf.picku(better, u0, v0, u1, v1, u2, v2, fu, fv, ad, buv), sel(~U32, better, tan, btn), sel(~U32, better, geo, bge), sel(~F32, better, le, ble))
    case 1n+f False{} True{} _ _ _ _ _ _ _ _ _ TNil{}:
      Walk.go(f, False{}, False{}, True{}, False{}, False{}, False{}, False{}, U32.is_eq(todo, 0), False{}, (v >= 1 : U32), root, root, TNil{}, s1, s2, s3, s4, s5, s6, root, 0, 0, path, pw, d, todo, v, any, ox, oy, oz, dx, dy, dz, ix, iy, iz, bt, bnx, bny, bnz, bc, buv, btn, bge, ble)
    case 1n+f False{} False{} False{} False{} False{} True{} False{} _ _ _ _ _:
      Walk.go(f, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, root, cur, TNil{}, cr, s1, s2, s3, s4, s5, root, 0, 0, path, pw, d, todo, v, any, ox, oy, oz, dx, dy, dz, ix, iy, iz, bt, bnx, bny, bnz, bc, buv, btn, bge, ble)
    case 1n+f False{} False{} False{} False{} False{} True{} True{} _ _ _ _ _:
      Walk.go(f, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, root, cr, TNil{}, cur, s1, s2, s3, s4, s5, root, 0, 0, (path + pw / 2 : U32), pw, d, todo, v, any, ox, oy, oz, dx, dy, dz, ix, iy, iz, bt, bnx, bny, bnz, bc, buv, btn, bge, ble)
    case 1n+f False{} False{} False{} False{} True{} False{} _ _ _ _ _ _:
      Walk.go(f, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, root, cr, TNil{}, s1, s2, s3, s4, s5, s6, root, 0, 0, path, pw, d, todo, v, any, ox, oy, oz, dx, dy, dz, ix, iy, iz, bt, bnx, bny, bnz, bc, buv, btn, bge, ble)
    case 1n+f False{} False{} False{} False{} False{} False{} _ _ False{} _ BNode{_, _, _, _, _, _, _, _, _, _, _, _, l, _} _:
      +k2 = (k - 1 : U32)
      Walk.go(f, False{}, False{}, False{}, U32.is_eq(k2, 0), False{}, False{}, False{}, False{}, U32.is_eq((rest .&. 1 : U32), 1), False{}, root, l, TNil{}, s1, s2, s3, s4, s5, s6, root, k2, (rest / 2 : U32), path, pw, d, todo, v, any, ox, oy, oz, dx, dy, dz, ix, iy, iz, bt, bnx, bny, bnz, bc, buv, btn, bge, ble)
    case 1n+f False{} False{} False{} False{} False{} False{} _ _ True{} _ BNode{_, _, _, _, _, _, _, _, _, _, _, _, _, r} _:
      +k2 = (k - 1 : U32)
      Walk.go(f, False{}, False{}, False{}, U32.is_eq(k2, 0), False{}, False{}, False{}, False{}, U32.is_eq((rest .&. 1 : U32), 1), False{}, root, r, TNil{}, s1, s2, s3, s4, s5, s6, root, k2, (rest / 2 : U32), path, pw, d, todo, v, any, ox, oy, oz, dx, dy, dz, ix, iy, iz, bt, bnx, bny, bnz, bc, buv, btn, bge, ble)
    case 1n+f False{} False{} False{} True{} _ _ _ _ _ _ BLeaf{ts} _:
      Walk.go(f, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, root, root, ts, s1, s2, s3, s4, s5, s6, root, 0, 0, path, pw, d, todo, v, any, ox, oy, oz, dx, dy, dz, ix, iy, iz, bt, bnx, bny, bnz, bc, buv, btn, bge, ble)
    case 1n+f False{} False{} False{} True{} _ _ _ _ _ _ BNode{lx0, ly0, lz0, lx1, ly1, lz1, rx0, ry0, rz0, rx1, ry1, rz1, l, r} _:
      +el = Slab.enter(lx0, ly0, lz0, lx1, ly1, lz1, ox, oy, oz, ix, iy, iz, bt)
      +er = Slab.enter(rx0, ry0, rz0, rx1, ry1, rz1, ox, oy, oz, ix, iy, iz, bt)
      +vl = (el < 1000000000.0 : F32)
      +vr = (er < 1000000000.0 : F32)
      +both = (vl && vr)
      +some = (vl || vr)
      +near = (both && (er < el : F32))
      +todo2 = sel(~U32, some, (todo * 2 + sel(~U32, both, 1, 0) : U32), todo)
      +v2 = sel(~U32, both, sel(~U32, (v >= 6 : U32), 6, (v + 1 : U32)), v)
      Walk.go(f, False{}, False{}, Bool.not(some), (vl && Bool.not(vr)), (vr && Bool.not(vl)), both, near, U32.is_eq(todo2, 0), False{}, (v2 >= 1 : U32), root, l, TNil{}, s1, s2, s3, s4, s5, s6, r, 0, 0, sel(~U32, vl, path, sel(~U32, vr, (path + pw : U32), path)), sel(~U32, some, (pw * 2 : U32), pw), sel(~U32, some, (d + 1 : U32), d), todo2, v2, any, ox, oy, oz, dx, dy, dz, ix, iy, iz, bt, bnx, bny, bnz, bc, buv, btn, bge, ble)
    case _ False{} False{} True{} _ _ _ _ True{} _ _ _ _:
      Hit{bt, bnx, bny, bnz, bc, buv, btn, bge, ble}
    case 1n+f False{} False{} True{} _ _ _ _ False{} _ True{} _ _:
      +low = (todo .&. (0 - todo) : U32)
      +pw2 = (pw / low : U32)
      +path2 = ((path % pw2) .^. (pw2 / 2 : U32) : U32)
      Walk.go(f, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, root, s1, TNil{}, s2, s3, s4, s5, s6, root, root, 0, 0, path2, pw2, (d - Walk.log2(low) : U32), ((todo / low : U32) - 1 : U32), (v - 1 : U32), any, ox, oy, oz, dx, dy, dz, ix, iy, iz, bt, bnx, bny, bnz, bc, buv, btn, bge, ble)
    case 1n+f False{} False{} True{} _ _ _ _ False{} _ False{} _ _:
      +low = (todo .&. (0 - todo) : U32)
      +pw2 = (pw / low : U32)
      +d2 = (d - Walk.log2(low) : U32)
      +path2 = ((path % pw2) .^. (pw2 / 2 : U32) : U32)
      Walk.go(f, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, U32.is_eq((path2 .&. 1 : U32), 1), False{}, root, root, TNil{}, root, root, root, root, root, root, root, d2, (path2 / 2 : U32), path2, pw2, d2, ((todo / low : U32) - 1 : U32), 0, any, ox, oy, oz, dx, dy, dz, ix, iy, iz, bt, bnx, bny, bnz, bc, buv, btn, bge, ble)
    case _ _ _ _ _ _ _ _ _ _ _ _ _:
      Hit{bt, bnx, bny, bnz, bc, buv, btn, bge, ble}

def Ray.cast(+scene: Bvh, +ox: F32, +oy: F32, +oz: F32, +dx: F32, +dy: F32, +dz: F32, +tp: F32, any: Bool) -> Hit:
  Walk.go(65536n, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, scene, scene, TNil{}, scene, scene, scene, scene, scene, scene, scene, 0, 0, 0, 1, 0, 0, 0, any, ox, oy, oz, dx, dy, dz, (1.0 / dx : F32), (1.0 / dy : F32), (1.0 / dz : F32), tp, 0.0, 1.0, 0.0, 0, 0, 0, 0, 0.0)

def Pose.mix(a: List<&2, Trs>, b: List<&2, Trs>, +t: F32) -> List<&2, Trs>:
  match a b:
    case x <> xs y <> ys:
      Trs.mix(x, y, t) <> Pose.mix(xs, ys, t)
    case _ _:
      Nil{}

def Pal.at(+t: Tree4<Mat4>, +i: U32) -> Mat4:
  Tree4.at(Mat4, 4n, t, i, Mat4.id())

def Pal.set(t: Tree4<Mat4>, +i: U32, v: Mat4) -> Tree4<Mat4>:
  Tree4.set(Mat4, 4n, t, i, v)

def Pose.rest(joints: List<&2, Joint>) -> List<&2, Trs>:
  match joints:
    case Nil{}:
      Nil{}
    case Joint{_, _, _, rest, _} <> more:
      Xform{t, r, s} = rest
      Trs{t, r, s} <> Pose.rest(more)

def Clip.at(+keys: List<&2, Trs>, +s: U32, +joints: U32) -> List<&2, Trs>:
  List.take(&2, Trs, List.drop(&2, Trs, keys, U32.to_nat((s * joints : U32))), U32.to_nat(joints))

def Clip.sample(+clip: Clip, +frame: U32, +fps: U32) -> List<&2, Trs>:
  Clip{_, _, rate, samples, joints, keys} = clip
  +ticks = (frame * rate : U32)
  +s = ((ticks / fps) % samples : U32)
  +s1 = ((s + 1) % samples : U32)
  +frac = (U32.to_f32((ticks % fps : U32)) / U32.to_f32(fps) : F32)
  Pose.mix(Clip.at(keys, s, joints), Clip.at(keys, s1, joints), frac)

def Skin.blend(+pal: Tree4<Mat4>, +p: Vec3, +n: Vec3, +j: U32, +w: F32) -> Vec3 & Vec3:
  +m = Pal.at(pal, j)
  (Vec3.scale(Mat4.transform_point(m, p), w), Vec3.scale(Mat4.transform_dir(m, n), w))

def Skin.sum(a: Vec3 & Vec3, b: Vec3 & Vec3) -> Vec3 & Vec3:
  (ap, an) = a
  (bp, bn) = b
  (Vec3.add(ap, bp), Vec3.add(an, bn))

def Skin.root(+root: Mat4, +p: Vec3, +n: Vec3, +w: F32) -> Vec3 & Vec3:
  (Vec3.scale(Mat4.transform_point(root, p), w), Vec3.scale(Mat4.transform_dir(root, n), w))

def Skin.fin(+v: Vert, r: Vec3 & Vec3) -> Vert:
  Vert{_, _, uv, j, w} = v
  (p, n) = r
  Vert{p, Vec3.normalize(n), uv, j, w}

def Skin.vert(+pal: Tree4<Mat4>, +root: Mat4, +v: Vert) -> Vert:
  Vert{p, n, _, jw, w} = v
  Vec4{w0, w1, w2, w3} = w
  Skin.fin(v, Skin.sum(Skin.root(root, p, n, (1.0 - (w0 + w1 + w2 + w3) : F32)), Skin.sum(Skin.sum(Skin.blend(pal, p, n, (jw .&. 255 : U32), w0), Skin.blend(pal, p, n, ((jw >> 8n) .&. 255 : U32), w1)), Skin.sum(Skin.blend(pal, p, n, ((jw >> 16n) .&. 255 : U32), w2), Skin.blend(pal, p, n, ((jw >> 24n) .&. 255 : U32), w3)))))

def Skin.walk(+pal: Tree4<Mat4>, +root: Mat4, t: Tree4<Vert>) -> Tree4<Vert>:
  match t:
    case T4Nil{}:
      T4Nil{}
    case T4Leaf{v}:
      T4Leaf{Skin.vert(pal, root, v)}
    case T4Qua{a, b, c, d}:
      T4Qua{Skin.walk(pal, root, a), Skin.walk(pal, root, b), Skin.walk(pal, root, c), Skin.walk(pal, root, d)}

def Skin.tree(+k: Nat, +pal: Tree4<Mat4>, +root: Mat4, t: Tree4<Vert>) -> Tree4<Vert>:
  match k t:
    case 0n other:
      Skin.walk(pal, root, other)
    case _ T4Nil{}:
      T4Nil{}
    case _ T4Leaf{v}:
      T4Leaf{Skin.vert(pal, root, v)}
    case 1n+j T4Qua{a, b, c, d}:
      w x y z = Skin.tree(j, pal, root, a) Skin.tree(j, pal, root, b) Skin.tree(j, pal, root, c) Skin.tree(j, pal, root, d)
      T4Qua{w, x, y, z}

def Skin.prims(+k: Nat, +pal: Tree4<Mat4>, +root: Mat4, prims: List<&2, Prim>) -> List<&2, Prim>:
  match prims:
    case Nil{}:
      Nil{}
    case Prim{mat, skin, depth, verts, ids} <> rest:
      Prim{mat, skin, depth, Skin.tree(k, pal, root, verts), ids} <> Skin.prims(k, pal, root, rest)

def Skin.joints(s: Skin) -> List<&2, Joint>:
  Skin{joints} = s
  joints

type Lights is Data:
  LNil{}
  LLeaf{+x0: F32, +y0: F32, +z0: F32, +ax: F32, +ay: F32, +az: F32, +bx: F32, +by: F32, +bz: F32, +w: F32, +le: F32, +mat: U32, +er: F32, +eg: F32, +eb: F32}
  LNode{+w: F32, +wl: F32, l: Lights, r: Lights}

def World() -> Type:
  Bvh & (Mats & Lights)

type LS is Data:
  LS{t: Lights, +w: F32}

def Lights.add(emits: Bool, +x0: F32, +y0: F32, +z0: F32, +ax: F32, +ay: F32, +az: F32, +bx: F32, +by: F32, +bz: F32, +le: F32, +mat: U32, acc: List<&2, LS>) -> List<&2, LS>:
  match emits:
    case False{}:
      acc
    case True{}:
      +cx = (ay * bz - az * by : F32)
      +cy = (az * bx - ax * bz : F32)
      +cz = (ax * by - ay * bx : F32)
      +w = (F32.sqrt((cx * cx + cy * cy + cz * cz : F32)) * 0.5 * le : F32)
      LS{LLeaf{x0, y0, z0, ax, ay, az, bx, by, bz, w, le, mat, 0.0, 0.0, 0.0}, w} <> acc

def Lights.of(+ts: Tris, acc: List<&2, LS>) -> List<&2, LS>:
  match ts:
    case TNil{}:
      acc
    case TCons{x0, y0, z0, ax, ay, az, bx, by, bz, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, col, _, _, le, next}:
      Lights.of(next, Lights.add((le > 0.0 : F32), x0, y0, z0, ax, ay, az, bx, by, bz, le, (col / 16777216 : U32), acc))

def Em.at(ems: List<&2, Em>, +i: U32) -> Em:
  Maybe.default(&2, Em, List.get(&2, Em, ems, U32.to_nat(i)), Em{0.0, 0.0, 0.0, 0.0})

def Lights.col(e: Em, +x0: F32, +y0: F32, +z0: F32, +ax: F32, +ay: F32, +az: F32, +bx: F32, +by: F32, +bz: F32, +w: F32, +le: F32, +mat: U32, acc: List<&2, LS>) -> List<&2, LS>:
  Em{_, er, eg, eb} = e
  LS{LLeaf{x0, y0, z0, ax, ay, az, bx, by, bz, w, le, mat, er, eg, eb}, w} <> acc

def Lights.fill(xs: List<&2, LS>, +ems: List<&2, Em>, acc: List<&2, LS>) -> List<&2, LS>:
  match xs:
    case LS{LLeaf{x0, y0, z0, ax, ay, az, bx, by, bz, w, le, +mat, _, _, _}, _} <> rest:
      Lights.fill(rest, ems, Lights.col(Em.at(ems, mat), x0, y0, z0, ax, ay, az, bx, by, bz, w, le, mat, acc))
    case _ <> rest:
      Lights.fill(rest, ems, acc)
    case Nil{}:
      acc

def LS.join(a: LS, b: LS) -> LS:
  LS{ta, wa} = a
  LS{tb, wb} = b
  +w = (wa + wb : F32)
  LS{LNode{w, wa, ta, tb}, w}

def LS.lone(a: LS) -> LS:
  LS{t, +w} = a
  LS{LNode{w, w, t, LNil{}}, w}

def LS.tree(a: LS) -> Lights:
  LS{t, _} = a
  t

def Lights.made(leaves: List<&2, LS>, +ems: List<&2, Em>) -> LS:
  Pairs.up(~LS, ~LS.join, ~LS.lone, ~LS{LNil{}, 0.0}, 32n, List.reverse(&2, LS, Lights.fill(leaves, ems, Nil{})))

def Lights.build(leaves: List<&2, LS>, +ems: List<&2, Em>) -> Lights:
  LS.tree(Lights.made(leaves, ems))

def Rng.next(+s: U32) -> U32:
  +a = (s .^. (s * 8192) : U32)
  +b = (a .^. (a / 131072) : U32)
  (b .^. (b * 32) : U32)

def Rng.unit(+s: U32) -> F32:
  (U32.to_f32((s / 256 : U32)) * 0.000000059604645 : F32)

def Rng.seed(+x: U32, +y: U32) -> U32:
  Rng.next(((x * 73856093) .^. (y * 19349663) .^. 2463534242 : U32))

def Sun.x() -> F32:
  (0.0 - 0.356 : F32)

def Sun.y() -> F32:
  0.815

def Sun.z() -> F32:
  0.458

def Sky.sun(+dx: F32, +dy: F32, +dz: F32) -> F32:
  sel(~F32, (dx * Sun.x() + dy * Sun.y() + dz * Sun.z() > 0.9928 : F32), 200.0, 0.0)

def Sky.r(+dy: F32, +sun: F32) -> F32:
  +u = F32.clamp(dy, 0.0, 1.0)
  (0.42 - 0.27 * u + sun : F32)

def Sky.g(+dy: F32, +sun: F32) -> F32:
  +u = F32.clamp(dy, 0.0, 1.0)
  (0.50 - 0.22 * u + 0.95 * sun : F32)

def Sky.b(+dy: F32, +sun: F32) -> F32:
  +u = F32.clamp(dy, 0.0, 1.0)
  (0.70 - 0.10 * u + 0.85 * sun : F32)

type PList is Data:
  PNil{}
  PCons{+i: U32, +x: U32, +y: U32, +ox: F32, +oy: F32, +oz: F32, +dx: F32, +dy: F32, +dz: F32, +tr: F32, +tg: F32, +tb: F32, +pd: F32, +ar: F32, +ag: F32, +ab: F32, +n: U32, +depth: U32, +seed: U32, next: PList}

type PT is Data:
  PLeaf{ps: PList}
  PQua{a: PT, b: PT, c: PT, d: PT}

def Live() -> Type:
  PT & World()

def Path.fresh(+i: U32, +x: U32, +y: U32, +ar: F32, +ag: F32, +ab: F32, +n: U32, +seed: U32, acc: PList) -> PList:
  PCons{i, x, y, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0, ar, ag, ab, n, none(), seed, acc}

def Path.done(+i: U32, +x: U32, +y: U32, +ar: F32, +ag: F32, +ab: F32, +n: U32, +seed: U32, acc: PList) -> PList:
  Path.fresh(i, x, y, ar, ag, ab, (n + 1 : U32), seed, acc)

def Path.lit(h: Hit, hs: Hit, hl: Hit, last: Bool, +i: U32, +x: U32, +y: U32, +ox: F32, +oy: F32, +oz: F32, +dx: F32, +dy: F32, +dz: F32, +tr: F32, +tg: F32, +tb: F32, +pd: F32, +ar: F32, +ag: F32, +ab: F32, +n: U32, +depth: U32, +seed: U32, +kr: F32, +kg: F32, +kb: F32, +qr: F32, +qg: F32, +qb: F32, +ld: F32, +lr: F32, +lg: F32, +lb: F32, acc: PList) -> PList:
  match h hs hl last:
    case Hit{t, _, _, _, _, _, _, _, _} Hit{ts, _, _, _, _, _, _, _, _} Hit{tl, _, _, _, _, _, _, _, _} True{}:
      +k = sel(~F32, (t >= 1000000000.0 : F32), 1.0, 0.0)
      +q = sel(~F32, (ts >= 1000000000.0 : F32), 1.0, 0.0)
      +l = sel(~F32, (tl >= ld : F32), 1.0, 0.0)
      Path.done(i, x, y, (ar + kr * k + qr * q + lr * l : F32), (ag + kg * k + qg * q + lg * l : F32), (ab + kb * k + qb * q + lb * l : F32), n, seed, acc)
    case Hit{t, _, _, _, _, _, _, _, _} Hit{ts, _, _, _, _, _, _, _, _} Hit{tl, _, _, _, _, _, _, _, _} False{}:
      +k = sel(~F32, (t >= 1000000000.0 : F32), 1.0, 0.0)
      +q = sel(~F32, (ts >= 1000000000.0 : F32), 1.0, 0.0)
      +l = sel(~F32, (tl >= ld : F32), 1.0, 0.0)
      PCons{i, x, y, ox, oy, oz, dx, dy, dz, tr, tg, tb, pd, (ar + kr * k + qr * q + lr * l : F32), (ag + kg * k + qg * q + lg * l : F32), (ab + kb * k + qb * q + lb * l : F32), n, depth, seed, acc}

def Brdf.d(+a2: F32, +ndh: F32) -> F32:
  +q = (ndh * ndh * (a2 - 1.0) + 1.0 : F32)
  (a2 / (3.1415927 * q * q : F32) : F32)

def Brdf.g1(+k: F32, +c: F32) -> F32:
  (c / (c * (1.0 - k) + k : F32) : F32)

def Brdf.spec(+a: F32, +ndl: F32, +ndv: F32, +ndh: F32) -> F32:
  +k = (a * 0.5 : F32)
  (Brdf.d((a * a : F32), ndh) * Brdf.g1(k, ndl) * Brdf.g1(k, ndv) / (4.0 * ndl * ndv : F32) : F32)

def Brdf.fw(+vdh: F32) -> F32:
  +q = (1.0 - F32.clamp(vdh, 0.0, 1.0) : F32)
  +q2 = (q * q : F32)
  (q2 * q2 * q : F32)

def Brdf.chan(+cd: F32, +f0: F32, +sp: F32, +fw: F32) -> F32:
  +f = (f0 + (1.0 - f0) * fw : F32)
  (cd * 0.3183099 * (1.0 - f) + sp * f : F32)

type Draw is Data:
  Draw{+px: F32, +py: F32, +pz: F32, +nx: F32, +ny: F32, +nz: F32, +pa: F32, +er: F32, +eg: F32, +eb: F32}

def Draw.none() -> Draw:
  Draw{0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0}

def Light.total(lights: Lights) -> F32:
  match lights:
    case LNil{}:
      0.0
    case LLeaf{_, _, _, _, _, _, _, _, _, w, _, _, _, _, _}:
      w
    case LNode{w, _, _, _}:
      w

def Light.leaf(+x0: F32, +y0: F32, +z0: F32, +ax: F32, +ay: F32, +az: F32, +bx: F32, +by: F32, +bz: F32, +le: F32, +er: F32, +eg: F32, +eb: F32, +u1: F32, +u2: F32, +ltot: F32) -> Draw:
  +s = F32.sqrt(u1)
  +ka = (s * (1.0 - u2) : F32)
  +kb = (s * u2 : F32)
  +cx = (ay * bz - az * by : F32)
  +cy = (az * bx - ax * bz : F32)
  +cz = (ax * by - ay * bx : F32)
  +il = (1.0 / F32.max(0.000001, F32.sqrt((cx * cx + cy * cy + cz * cz : F32))) : F32)
  Draw{(x0 + ka * ax + kb * bx : F32), (y0 + ka * ay + kb * by : F32), (z0 + ka * az + kb * bz : F32), (cx * il : F32), (cy * il : F32), (cz * il : F32), (le / ltot : F32), er, eg, eb}

def Light.pick(fuel: Nat, l: Lights, +x: F32, +u1: F32, +u2: F32, +ltot: F32) -> Draw:
  match fuel l:
    case 0n _:
      Draw.none()
    case 1n+f LNode{_, wl, a, b}:
      +left = (x < wl : F32)
      Light.pick(f, sel(~Lights, left, a, b), sel(~F32, left, x, (x - wl : F32)), u1, u2, ltot)
    case 1n+f LLeaf{x0, y0, z0, ax, ay, az, bx, by, bz, _, le, _, er, eg, eb}:
      Light.leaf(x0, y0, z0, ax, ay, az, bx, by, bz, le, er, eg, eb, u1, u2, ltot)
    case 1n+f LNil{}:
      Draw.none()

def Light.draw(has: Bool, +lights: Lights, +x: F32, +u1: F32, +u2: F32, +ltot: F32) -> Draw:
  match has:
    case False{}:
      Draw.none()
    case True{}:
      Light.pick(40n, lights, x, u1, u2, ltot)

def Path.dir(em: Draw, last: Bool, +scene: Bvh, +i: U32, +x: U32, +y: U32, +px: F32, +py: F32, +pz: F32, +nx: F32, +ny: F32, +nz: F32, +gx: F32, +gy: F32, +gz: F32, +vx: F32, +vy: F32, +vz: F32, +cr: F32, +cg: F32, +cb: F32, +metal: F32, +rough: F32, +tr: F32, +tg: F32, +tb: F32, +ar: F32, +ag: F32, +ab: F32, +n: U32, +depth: U32, +seed: U32, +yp: F32, +pt: Portal, acc: PList) -> PList:
  Draw{+epx, +epy, +epz, +enx, +eny, +enz, +epa, +eer, +eeg, +eeb} = em
  Portal{kx0, kz0, kx1, kz1, ky} = pt
  +s1 = Rng.next(seed)
  +s2 = Rng.next(s1)
  +s3 = Rng.next(s2)
  +s4 = Rng.next(s3)
  +s5 = Rng.next(s4)
  +a = F32.max(0.01, (rough * rough : F32))
  +a2 = (a * a : F32)
  +ps = (0.1 + 0.9 * metal : F32)
  +spec = (Rng.unit(s1) < ps : F32)
  +u2 = Rng.unit(s2)
  +phi = (6.2831853 * Rng.unit(s3) : F32)
  +cphi = F32.cos(phi)
  +sphi = F32.sin(phi)
  +rr = F32.sqrt(u2)
  +rz = F32.sqrt(F32.max(0.0, (1.0 - u2 : F32)))
  +ch = F32.sqrt(((1.0 - u2) / (1.0 + (a2 - 1.0) * u2) : F32))
  +sh = F32.sqrt(F32.max(0.0, (1.0 - ch * ch : F32)))
  +nup = (F32.max(nx, (0.0 - nx : F32)) > 0.9 : F32)
  +nax = sel(~F32, nup, 0.0, 1.0)
  +nay = sel(~F32, nup, 1.0, 0.0)
  +ncx = (nay * nz : F32)
  +ncy = (0.0 - nax * nz : F32)
  +ncw = (nax * ny - nay * nx : F32)
  +nfl = (1.0 / F32.max(0.000001, F32.sqrt((ncx * ncx + ncy * ncy + ncw * ncw : F32))) : F32)
  +ntx = (ncx * nfl : F32)
  +nty = (ncy * nfl : F32)
  +ntz = (ncw * nfl : F32)
  +nbx = (ny * ntz - nz * nty : F32)
  +nby = (nz * ntx - nx * ntz : F32)
  +nbz = (nx * nty - ny * ntx : F32)
  +mhx = (sh * cphi : F32)
  +mhy = (sh * sphi : F32)
  +mx = (ntx * mhx + nbx * mhy + nx * ch : F32)
  +my = (nty * mhx + nby * mhy + ny * ch : F32)
  +mz = (ntz * mhx + nbz * mhy + nz * ch : F32)
  +vdm = (vx * mx + vy * my + vz * mz : F32)
  +lx = Ray.nz(sel(~F32, spec, (2.0 * vdm * mx - vx : F32), (ntx * (rr * cphi) + nbx * (rr * sphi) + nx * rz : F32)))
  +ly = Ray.nz(sel(~F32, spec, (2.0 * vdm * my - vy : F32), (nty * (rr * cphi) + nby * (rr * sphi) + ny * rz : F32)))
  +lz = Ray.nz(sel(~F32, spec, (2.0 * vdm * mz - vz : F32), (ntz * (rr * cphi) + nbz * (rr * sphi) + nz * rz : F32)))
  +ndl = (nx * lx + ny * ly + nz * lz : F32)
  +ndv = F32.max(0.001, (nx * vx + ny * vy + nz * vz : F32))
  +hl = (1.0 / F32.max(0.000001, F32.sqrt(((vx + lx) * (vx + lx) + (vy + ly) * (vy + ly) + (vz + lz) * (vz + lz) : F32))) : F32)
  +ndh = ((nx * (vx + lx) + ny * (vy + ly) + nz * (vz + lz)) * hl : F32)
  +vdh = ((vx * (vx + lx) + vy * (vy + ly) + vz * (vz + lz)) * hl : F32)
  +pdf = ((1.0 - ps) * F32.max(0.0, ndl) * 0.3183099 + ps * Brdf.d(a2, ndh) * ndh / (4.0 * F32.max(0.0001, vdh)) : F32)
  +ok = ((ndl > 0.0001) && (gx * lx + gy * ly + gz * lz > 0.0001) && (pdf > 0.0000001) : F32)
  +sp = Brdf.spec(a, F32.max(0.0001, ndl), ndv, ndh)
  +fw = Brdf.fw(vdh)
  +wk = sel(~F32, ok, (ndl / pdf : F32), 0.0)
  +m1 = (1.0 - metal : F32)
  +f0r = (0.04 + (cr - 0.04) * metal : F32)
  +f0g = (0.04 + (cg - 0.04) * metal : F32)
  +f0b = (0.04 + (cb - 0.04) * metal : F32)
  +ox = (px + gx * 0.001 : F32)
  +oy = (py + gy * 0.001 : F32)
  +oz = (pz + gz * 0.001 : F32)
  +cz = (1.0 - Rng.unit(s4) * 0.0072 : F32)
  +sn = F32.sqrt(F32.max(0.0, (1.0 - cz * cz : F32)))
  +wphi = (6.2831853 * Rng.unit(s5) : F32)
  +wx = (sn * F32.cos(wphi) : F32)
  +wy = (sn * F32.sin(wphi) : F32)
  +sux = Sun.x()
  +suy = Sun.y()
  +suz = Sun.z()
  +sup = (F32.max(sux, (0.0 - sux : F32)) > 0.9 : F32)
  +sax = sel(~F32, sup, 0.0, 1.0)
  +say = sel(~F32, sup, 1.0, 0.0)
  +scx = (say * suz : F32)
  +scy = (0.0 - sax * suz : F32)
  +scw = (sax * suy - say * sux : F32)
  +sfl = (1.0 / F32.max(0.000001, F32.sqrt((scx * scx + scy * scy + scw * scw : F32))) : F32)
  +stx = (scx * sfl : F32)
  +sty = (scy * sfl : F32)
  +stz = (scw * sfl : F32)
  +sbx = (suy * stz - suz * sty : F32)
  +sby = (suz * stx - sux * stz : F32)
  +sbz = (sux * sty - suy * stx : F32)
  +ldx = Ray.nz((stx * wx + sbx * wy + sux * cz : F32))
  +ldy = Ray.nz((sty * wx + sby * wy + suy * cz : F32))
  +ldz = Ray.nz((stz * wx + sbz * wy + suz * cz : F32))
  +cos = (nx * ldx + ny * ldy + nz * ldz : F32)
  +lit = ((cos > 0.0) && (gx * ldx + gy * ldy + gz * ldz > 0.0) : F32)
  +sl = (1.0 / F32.max(0.000001, F32.sqrt(((vx + ldx) * (vx + ldx) + (vy + ldy) * (vy + ldy) + (vz + ldz) * (vz + ldz) : F32))) : F32)
  +sndh = ((nx * (vx + ldx) + ny * (vy + ldy) + nz * (vz + ldz)) * sl : F32)
  +ssp = Brdf.spec(a, F32.max(0.0001, cos), ndv, sndh)
  +sfw = Brdf.fw(((vx * (vx + ldx) + vy * (vy + ldy) + vz * (vz + ldz)) * sl : F32))
  +sk = sel(~F32, lit, (cos * 200.0 * 0.0452 : F32), 0.0)
  +tp = sel(~F32, ((ldy < 0.0) && (oy > yp) : F32), ((yp - oy) / ldy : F32), 1000000000.0)
  +s6 = Rng.next(s5)
  +s7 = Rng.next(s6)
  +area = F32.max(0.000001, ((kx1 - kx0) * (kz1 - kz0) : F32))
  +qx = (kx0 + Rng.unit(s6) * (kx1 - kx0) - ox : F32)
  +qy = (ky - oy : F32)
  +qz = (kz0 + Rng.unit(s7) * (kz1 - kz0) - oz : F32)
  +qd2 = (qx * qx + qy * qy + qz * qz : F32)
  +qd = F32.sqrt(qd2)
  +qi = (1.0 / F32.max(0.000001, qd) : F32)
  +ex = Ray.nz((qx * qi : F32))
  +ey = Ray.nz((qy * qi : F32))
  +ez = Ray.nz((qz * qi : F32))
  +ecos = (nx * ex + ny * ey + nz * ez : F32)
  +elit = ((ecos > 0.0) && (gx * ex + gy * ey + gz * ez > 0.0) && (qy > 0.0001) : F32)
  +el = (1.0 / F32.max(0.000001, F32.sqrt(((vx + ex) * (vx + ex) + (vy + ey) * (vy + ey) + (vz + ez) * (vz + ez) : F32))) : F32)
  +endh = ((nx * (vx + ex) + ny * (vy + ey) + nz * (vz + ez)) * el : F32)
  +evdh = ((vx * (vx + ex) + vy * (vy + ey) + vz * (vz + ez)) * el : F32)
  +esp = Brdf.spec(a, F32.max(0.0001, ecos), ndv, endh)
  +efw = Brdf.fw(evdh)
  +epp = (qd2 / (area * F32.max(0.0001, ey)) : F32)
  +epb = ((1.0 - ps) * F32.max(0.0, ecos) * 0.3183099 + ps * Brdf.d(a2, endh) * endh / (4.0 * F32.max(0.0001, evdh)) : F32)
  +ek = sel(~F32, elit, (ecos / (epp + epb) : F32), 0.0)
  +wr = (tr * Brdf.chan((cr * m1 : F32), f0r, sp, fw) * wk : F32)
  +wg = (tg * Brdf.chan((cg * m1 : F32), f0g, sp, fw) * wk : F32)
  +wb = (tb * Brdf.chan((cb * m1 : F32), f0b, sp, fw) * wk : F32)
  +s8 = Rng.next(s7)
  +jx = (epx - ox : F32)
  +jy = (epy - oy : F32)
  +jz = (epz - oz : F32)
  +jd2 = (jx * jx + jy * jy + jz * jz : F32)
  +jd = F32.sqrt(jd2)
  +ji = (1.0 / F32.max(0.000001, jd) : F32)
  +dlx = Ray.nz((jx * ji : F32))
  +dly = Ray.nz((jy * ji : F32))
  +dlz = Ray.nz((jz * ji : F32))
  +lcos = (nx * dlx + ny * dly + nz * dlz : F32)
  +lnd = (enx * dlx + eny * dly + enz * dlz : F32)
  +lcl = F32.max(lnd, (0.0 - lnd : F32))
  +llit = ((lcos > 0.0) && (gx * dlx + gy * dly + gz * dlz > 0.0) && (epa > 0.0) && (lcl > 0.0001) && (jd > 0.002) : F32)
  +ll = (1.0 / F32.max(0.000001, F32.sqrt(((vx + dlx) * (vx + dlx) + (vy + dly) * (vy + dly) + (vz + dlz) * (vz + dlz) : F32))) : F32)
  +lndh = ((nx * (vx + dlx) + ny * (vy + dly) + nz * (vz + dlz)) * ll : F32)
  +lvdh = ((vx * (vx + dlx) + vy * (vy + dly) + vz * (vz + dlz)) * ll : F32)
  +lsp = Brdf.spec(a, F32.max(0.0001, lcos), ndv, lndh)
  +lfw = Brdf.fw(lvdh)
  +lpl = (epa * jd2 / F32.max(0.0001, lcl) : F32)
  +lpb = ((1.0 - ps) * F32.max(0.0, lcos) * 0.3183099 + ps * Brdf.d(a2, lndh) * lndh / (4.0 * F32.max(0.0001, lvdh)) : F32)
  +lk = sel(~F32, llit, (lcos / (lpl + lpb) : F32), 0.0)
  +ld = sel(~F32, llit, (jd * 0.999 : F32), 1.0)
  +ltp = sel(~F32, ((dly < 0.0) && (oy > yp) : F32), ((yp - oy) / dly : F32), 1000000000.0)
  +q = sel(~F32, (depth >= 2 : U32), F32.clamp(F32.max(wr, F32.max(wg, wb)), 0.05, 1.0), 1.0)
  +live = (Rng.unit(s8) < q : F32)
  +iq = (1.0 / q : F32)
  Path.lit(Ray.cast(scene, ox, oy, oz, ldx, ldy, ldz, sel(~F32, lit, tp, 0.0), True{}), Ray.cast(scene, ox, oy, oz, ex, ey, ez, sel(~F32, elit, 1000000000.0, 0.0), True{}), Ray.cast(scene, ox, oy, oz, dlx, dly, dlz, sel(~F32, llit, F32.min(ld, ltp), 0.0), True{}), (last || Bool.not(ok) || Bool.not(live)), i, x, y, ox, oy, oz, lx, ly, lz, (wr * iq : F32), (wg * iq : F32), (wb * iq : F32), pdf, ar, ag, ab, n, (depth + 1 : U32), s8, (tr * Brdf.chan((cr * m1 : F32), f0r, ssp, sfw) * sk : F32), (tg * 0.95 * Brdf.chan((cg * m1 : F32), f0g, ssp, sfw) * sk : F32), (tb * 0.85 * Brdf.chan((cb * m1 : F32), f0b, ssp, sfw) * sk : F32), (tr * Brdf.chan((cr * m1 : F32), f0r, esp, efw) * ek * Sky.r(ey, 0.0) : F32), (tg * Brdf.chan((cg * m1 : F32), f0g, esp, efw) * ek * Sky.g(ey, 0.0) : F32), (tb * Brdf.chan((cb * m1 : F32), f0b, esp, efw) * ek * Sky.b(ey, 0.0) : F32), ld, (tr * Brdf.chan((cr * m1 : F32), f0r, lsp, lfw) * lk * eer : F32), (tg * Brdf.chan((cg * m1 : F32), f0g, lsp, lfw) * lk * eeg : F32), (tb * Brdf.chan((cb * m1 : F32), f0b, lsp, lfw) * lk * eeb : F32), acc)

def Path.bounce(last: Bool, +scene: Bvh, +lights: Lights, +i: U32, +x: U32, +y: U32, +px: F32, +py: F32, +pz: F32, +nx: F32, +ny: F32, +nz: F32, +gx: F32, +gy: F32, +gz: F32, +vx: F32, +vy: F32, +vz: F32, +cr: F32, +cg: F32, +cb: F32, +metal: F32, +rough: F32, +tr: F32, +tg: F32, +tb: F32, +ar: F32, +ag: F32, +ab: F32, +n: U32, +depth: U32, +seed: U32, +yp: F32, +pt: Portal, acc: PList) -> PList:
  +ltot = Light.total(lights)
  +s9 = Rng.next(seed)
  +s10 = Rng.next(s9)
  +s11 = Rng.next(s10)
  Path.dir(Light.draw((ltot > 0.0 : F32), lights, (Rng.unit(s9) * ltot : F32), Rng.unit(s10), Rng.unit(s11), F32.max(0.000000001, ltot)), last, scene, i, x, y, px, py, pz, nx, ny, nz, gx, gy, gz, vx, vy, vz, cr, cg, cb, metal, rough, tr, tg, tb, ar, ag, ab, n, depth, s11, yp, pt, acc)

def Chan.of(+c: U32, +n: Nat) -> F32:
  (U32.to_f32(((c >> n : U32) .&. 255 : U32)) / 255.0 : F32)

def Tex.pick4(right: Bool, low: Bool, +a: U32, +b: U32, +c: U32, +d: U32) -> U32:
  match right low:
    case False{} False{}:
      a
    case True{} False{}:
      b
    case False{} True{}:
      c
    case True{} True{}:
      d

def Tex.walk(t: Tex, right: Bool, low: Bool, +x: U32, +y: U32, +pw: U32) -> U32:
  match t right low:
    case TFlat{c} _ _:
      c
    case TLeaf{a, b, c, d} r l:
      Tex.pick4(r, l, a, b, c, d)
    case TNode{tl, _, _, _} False{} False{}:
      +pw2 = (pw / 2 : U32)
      Tex.walk(tl, U32.is_eq((x / pw2 % 2 : U32), 1), U32.is_eq((y / pw2 % 2 : U32), 1), x, y, pw2)
    case TNode{_, tr, _, _} True{} False{}:
      +pw2 = (pw / 2 : U32)
      Tex.walk(tr, U32.is_eq((x / pw2 % 2 : U32), 1), U32.is_eq((y / pw2 % 2 : U32), 1), x, y, pw2)
    case TNode{_, _, bl, _} False{} True{}:
      +pw2 = (pw / 2 : U32)
      Tex.walk(bl, U32.is_eq((x / pw2 % 2 : U32), 1), U32.is_eq((y / pw2 % 2 : U32), 1), x, y, pw2)
    case TNode{_, _, _, br} True{} True{}:
      +pw2 = (pw / 2 : U32)
      Tex.walk(br, U32.is_eq((x / pw2 % 2 : U32), 1), U32.is_eq((y / pw2 % 2 : U32), 1), x, y, pw2)

def Tex.fetch(t: Tex, +x: U32, +y: U32, +pw: U32) -> U32:
  Tex.walk(t, U32.is_eq((x / pw % 2 : U32), 1), U32.is_eq((y / pw % 2 : U32), 1), x, y, pw)

def Tex.sample(t: Tex, +pw: U32, +uv: U32, +jx: F32, +jy: F32) -> U32:
  +n = (pw * 2 : U32)
  +mask = (n - 1 : U32)
  +nf = U32.to_f32(n)
  +fx = (U32.to_f32((uv / 65536 : U32)) * 0.0000152590219 * nf + nf - 0.5 + jx : F32)
  +fy = (U32.to_f32((uv .&. 65535 : U32)) * 0.0000152590219 * nf + nf - 0.5 + jy : F32)
  Tex.fetch(t, (F32.to_u32(F32.floor(fx)) .&. mask : U32), (F32.to_u32(F32.floor(fy)) .&. mask : U32), pw)

type Mtl is Data:
  Mtl{+tc: U32, +tm: U32, +tn: U32, +metal: F32, +rough: F32, +ns: F32, +er: F32, +eg: F32, +eb: F32}

def Mats.at(ms: Mats, sel: Bool, +i: U32, +uv: U32, +jx: F32, +jy: F32) -> Mtl:
  match ms sel:
    case MtNone{} _:
      Mtl{16777215, 16777215, 8421631, 0.0, 1.0, 1.0, 0.0, 0.0, 0.0}
    case MtLeaf{pw, base, mpw, mr, npw, nrm, metal, rough, ns, er, eg, eb} _:
      Mtl{Tex.sample(base, pw, uv, jx, jy), Tex.sample(mr, mpw, uv, jx, jy), Tex.sample(nrm, npw, uv, jx, jy), metal, rough, ns, er, eg, eb}
    case MtNode{l, _} False{}:
      Mats.at(l, U32.is_eq(((i * 2 / 128) .&. 1 : U32), 1), ((i * 2) .&. 255 : U32), uv, jx, jy)
    case MtNode{_, r} True{}:
      Mats.at(r, U32.is_eq(((i * 2 / 128) .&. 1 : U32), 1), ((i * 2) .&. 255 : U32), uv, jx, jy)

def Tex.chan(+c: U32, +div: U32) -> F32:
  (U32.to_f32(((c / div : U32) .&. 255 : U32)) / 255.0 : F32)

def Tex.lin(+c: U32, +div: U32) -> F32:
  +s = Tex.chan(c, div)
  (s * s : F32)

def Tan.c(+t: U32, +div: U32) -> F32:
  (U32.to_f32(((t / div : U32) .&. 1023 : U32)) * 0.0019550342 - 1.0 : F32)

type Render is Data:
  Render{+maxd: U32, +mode: U32}

def Render.maxd(+r: Render) -> U32:
  Render{maxd, _} = r
  maxd

def Render.mode(+r: Render) -> U32:
  Render{_, mode} = r
  mode

def Path.shade(m: Mtl, +scene: Bvh, +lights: Lights, +i: U32, +x: U32, +y: U32, +ox: F32, +oy: F32, +oz: F32, +dx: F32, +dy: F32, +dz: F32, +t: F32, +nx: F32, +ny: F32, +nz: F32, +col: U32, +tan: U32, +geo: U32, +le: F32, +tr: F32, +tg: F32, +tb: F32, +pd: F32, +ar: F32, +ag: F32, +ab: F32, +n: U32, +depth: U32, +seed: U32, +yp: F32, +pt: Portal, +render: Render, acc: PList) -> PList:
  Mtl{+tc, +tm, +tn, +metal, +rough, +ns, +er, +eg, +eb} = m
  +ex = Tan.c(geo, 1048576)
  +ey = Tan.c(geo, 1024)
  +ez = Tan.c(geo, 1)
  +el = (1.0 / F32.max(0.000001, F32.sqrt((ex * ex + ey * ey + ez * ez : F32))) : F32)
  +s = sel(~F32, (ex * dx + ey * dy + ez * dz > 0.0 : F32), (0.0 - 1.0 : F32), 1.0)
  +gx = (s * el * ex : F32)
  +gy = (s * el * ey : F32)
  +gz = (s * el * ez : F32)
  +il = (s / F32.max(0.000001, F32.sqrt((nx * nx + ny * ny + nz * nz : F32))) : F32)
  +ix = (il * nx : F32)
  +iy = (il * ny : F32)
  +iz = (il * nz : F32)
  +tx = Tan.c(tan, 1048576)
  +ty = Tan.c(tan, 1024)
  +tz = Tan.c(tan, 1)
  +hw = sel(~F32, U32.is_eq(((tan / 1073741824 : U32) .&. 1 : U32), 1), 1.0, (0.0 - 1.0 : F32))
  +td = (ix * tx + iy * ty + iz * tz : F32)
  +qx = (tx - ix * td : F32)
  +qy = (ty - iy * td : F32)
  +qz = (tz - iz * td : F32)
  +ql = (1.0 / F32.max(0.000001, F32.sqrt((qx * qx + qy * qy + qz * qz : F32))) : F32)
  +ux = (qx * ql : F32)
  +uy = (qy * ql : F32)
  +uz = (qz * ql : F32)
  +bx = ((iy * uz - iz * uy) * hw : F32)
  +by = ((iz * ux - ix * uz) * hw : F32)
  +bz = ((ix * uy - iy * ux) * hw : F32)
  +mx = ((Tex.chan(tn, 65536) * 2.0 - 1.0) * ns : F32)
  +my = ((Tex.chan(tn, 256) * 2.0 - 1.0) * ns : F32)
  +mz = (Tex.chan(tn, 1) * 2.0 - 1.0 : F32)
  +wx = (ux * mx + bx * my + ix * mz : F32)
  +wy = (uy * mx + by * my + iy * mz : F32)
  +wz = (uz * mx + bz * my + iz * mz : F32)
  +wl = (1.0 / F32.max(0.000001, F32.sqrt((wx * wx + wy * wy + wz * wz : F32))) : F32)
  +wd = ((wx * gx + wy * gy + wz * gz) * wl : F32)
  +wk = F32.max(0.0, (0.05 - wd : F32))
  +fx = (wx * wl + gx * wk : F32)
  +fy = (wy * wl + gy * wk : F32)
  +fz = (wz * wl + gz * wk : F32)
  +fl = (1.0 / F32.max(0.000001, F32.sqrt((fx * fx + fy * fy + fz * fz : F32))) : F32)
  +ltot = Light.total(lights)
  +gcos = F32.max(0.0001, (0.0 - (gx * dx + gy * dy + gz * dz) : F32))
  +pl = sel(~F32, (ltot > 0.0 : F32), (le * t * t / (gcos * F32.max(0.000001, ltot)) : F32), 0.0)
  +lw = sel(~F32, U32.is_eq(depth, 0), 1.0, (pd / (pd + pl) : F32))
  Path.bounce(((depth + 1) >= Render.maxd(render) : U32), scene, lights, i, x, y, (ox + t * dx : F32), (oy + t * dy : F32), (oz + t * dz : F32), (fx * fl : F32), (fy * fl : F32), (fz * fl : F32), gx, gy, gz, (0.0 - dx : F32), (0.0 - dy : F32), (0.0 - dz : F32), (Tex.lin(tc, 65536) * Chan.of(col, 16n) : F32), (Tex.lin(tc, 256) * Chan.of(col, 8n) : F32), (Tex.lin(tc, 1) * Chan.of(col, 0n) : F32), (metal * Tex.chan(tm, 1) : F32), (rough * Tex.chan(tm, 256) : F32), tr, tg, tb, (ar + tr * er * lw : F32), (ag + tg * eg * lw : F32), (ab + tb * eb * lw : F32), n, depth, seed, yp, pt, acc)

def Path.met(miss: Bool, plain: Bool, +scene: Bvh, +mats: Mats, +lights: Lights, +i: U32, +x: U32, +y: U32, +ox: F32, +oy: F32, +oz: F32, +dx: F32, +dy: F32, +dz: F32, +t: F32, +nx: F32, +ny: F32, +nz: F32, +col: U32, +uv: U32, +tan: U32, +geo: U32, +le: F32, +tr: F32, +tg: F32, +tb: F32, +pd: F32, +ar: F32, +ag: F32, +ab: F32, +n: U32, +depth: U32, +seed: U32, +yp: F32, +pt: Portal, +render: Render, acc: PList) -> PList:
  match miss plain:
    case True{} _:
      Portal{kx0, kz0, kx1, kz1, ky} = pt
      +sun = sel(~F32, U32.is_eq(depth, 0), Sky.sun(dx, dy, dz), 0.0)
      +area = F32.max(0.000001, ((kx1 - kx0) * (kz1 - kz0) : F32))
      +tl = ((ky - oy) / dy : F32)
      +through = ((dy > 0.0001) && (tl > 0.0) && (ox + tl * dx >= kx0) && (ox + tl * dx <= kx1) && (oz + tl * dz >= kz0) && (oz + tl * dz <= kz1) : F32)
      +ppl = sel(~F32, through, (tl * tl / (area * dy) : F32), 0.0)
      +sw = sel(~F32, U32.is_eq(depth, 0), 1.0, (pd / (pd + ppl) : F32))
      Path.done(i, x, y, (ar + tr * sw * Sky.r(dy, sun) : F32), (ag + tg * sw * Sky.g(dy, sun) : F32), (ab + tb * sw * Sky.b(dy, sun) : F32), n, seed, acc)
    case False{} True{}:
      +px = (ox + t * dx : F32)
      +pz = (oz + t * dz : F32)
      +c = (F32.floor((px * 2.0 : F32)) + F32.floor((pz * 2.0 : F32)) : F32)
      +odd = F32.is_eq((c - 2.0 * F32.floor((c * 0.5 : F32)) : F32), 1.0)
      +g = sel(~F32, odd, 0.25, 0.7)
      Path.bounce(((depth + 1) >= Render.maxd(render) : U32), scene, lights, i, x, y, px, (oy + t * dy : F32), pz, 0.0, 1.0, 0.0, 0.0, 1.0, 0.0, (0.0 - dx : F32), (0.0 - dy : F32), (0.0 - dz : F32), g, g, g, 0.0, 1.0, tr, tg, tb, ar, ag, ab, n, depth, seed, yp, pt, acc)
    case False{} False{}:
      +s1 = Rng.next(seed)
      +s2 = Rng.next(s1)
      +mat = (col / 16777216 : U32)
      Path.shade(Mats.at(mats, U32.is_eq(((mat / 128 : U32) .&. 1 : U32), 1), (mat .&. 255 : U32), uv, Rng.unit(s1), Rng.unit(s2)), scene, lights, i, x, y, ox, oy, oz, dx, dy, dz, t, nx, ny, nz, col, tan, geo, le, tr, tg, tb, pd, ar, ag, ab, n, depth, s2, yp, pt, render, acc)

def Path.hit(h: Hit, +scene: Bvh, +mats: Mats, +lights: Lights, +i: U32, +x: U32, +y: U32, +ox: F32, +oy: F32, +oz: F32, +dx: F32, +dy: F32, +dz: F32, +tr: F32, +tg: F32, +tb: F32, +pd: F32, +ar: F32, +ag: F32, +ab: F32, +n: U32, +depth: U32, +seed: U32, +tp: F32, +yp: F32, +pt: Portal, +render: Render, acc: PList) -> PList:
  Hit{+t, nx, ny, nz, col, uv, tan, geo, le} = h
  Path.met((t >= 1000000000.0 : F32), F32.is_eq(t, tp), scene, mats, lights, i, x, y, ox, oy, oz, dx, dy, dz, t, nx, ny, nz, col, uv, tan, geo, le, tr, tg, tb, pd, ar, ag, ab, n, depth, seed, yp, pt, render, acc)

def Path.trace(+scene: Bvh, +mats: Mats, +lights: Lights, +i: U32, +x: U32, +y: U32, +ox: F32, +oy: F32, +oz: F32, +dx: F32, +dy: F32, +dz: F32, +tr: F32, +tg: F32, +tb: F32, +pd: F32, +ar: F32, +ag: F32, +ab: F32, +n: U32, +depth: U32, +seed: U32, +yp: F32, +pt: Portal, +render: Render, acc: PList) -> PList:
  +tp = sel(~F32, ((dy < 0.0) && (oy > yp) : F32), ((yp - oy) / dy : F32), 1000000000.0)
  Path.hit(Ray.cast(scene, ox, oy, oz, dx, dy, dz, tp, False{}), scene, mats, lights, i, x, y, ox, oy, oz, dx, dy, dz, tr, tg, tb, pd, ar, ag, ab, n, depth, seed, tp, yp, pt, render, acc)

type Cam is Data:
  Cam{+rx: F32, +ry: F32, +rz: F32, +ux: F32, +uy: F32, +uz: F32, +fx: F32, +fy: F32, +fz: F32, +ex: F32, +ey: F32, +ez: F32}

def Cam.basis(+yc: F32, +ys: F32, +pc: F32, +ps: F32, +ex: F32, +ey: F32, +ez: F32) -> Cam:
  Cam{yc, 0.0, ys, (ys * ps : F32), pc, (0.0 - yc * ps : F32), (0.0 - ys * pc : F32), ps, (yc * pc : F32), ex, ey, ez}

type V3 is Data:
  V3{x: F32, y: F32, z: F32}

def Cam.world(cam: Cam, +x: F32, +y: F32, +z: F32) -> V3:
  Cam{rx, ry, rz, ux, uy, uz, fx, fy, fz, _, _, _} = cam
  V3{(rx * x + ux * y + fx * z : F32), (ry * x + uy * y + fy * z : F32), (rz * x + uz * y + fz * z : F32)}

def Path.face(+nx: F32, +ny: F32, +nz: F32, +dx: F32, +dy: F32, +dz: F32) -> F32:
  +nd = (nx * dx + ny * dy + nz * dz : F32)
  (0.2 + 0.8 * F32.max(nd, (0.0 - nd : F32)) / F32.max(0.000001, F32.sqrt((nx * nx + ny * ny + nz * nz : F32))) : F32)

def Path.flat(h: Hit, +i: U32, +x: U32, +y: U32, +dx: F32, +dy: F32, +dz: F32, +ar: F32, +ag: F32, +ab: F32, +n: U32, +seed: U32, acc: PList) -> PList:
  Hit{+t, nx, ny, nz, _, _, _, _, _} = h
  +v = sel(~F32, (t >= 1000000000.0 : F32), 0.25, (0.8 * Path.face(nx, ny, nz, dx, dy, dz) : F32))
  Path.done(i, x, y, (ar + v : F32), (ag + v : F32), (ab + v : F32), n, seed, acc)

def Path.base(m: Mtl, +col: U32, +f: F32, +i: U32, +x: U32, +y: U32, +ar: F32, +ag: F32, +ab: F32, +n: U32, +seed: U32, acc: PList) -> PList:
  Mtl{+tc, _, _, _, _, _, _, _, _} = m
  Path.done(i, x, y, (ar + Tex.lin(tc, 65536) * Chan.of(col, 16n) * f : F32), (ag + Tex.lin(tc, 256) * Chan.of(col, 8n) * f : F32), (ab + Tex.lin(tc, 1) * Chan.of(col, 0n) * f : F32), n, seed, acc)

def Path.paint(miss: Bool, plain: Bool, +mats: Mats, +col: U32, +uv: U32, +f: F32, +px: F32, +pz: F32, +i: U32, +x: U32, +y: U32, +ar: F32, +ag: F32, +ab: F32, +n: U32, +seed: U32, acc: PList) -> PList:
  match miss plain:
    case True{} _:
      Path.done(i, x, y, (ar + 0.25 : F32), (ag + 0.25 : F32), (ab + 0.25 : F32), n, seed, acc)
    case False{} True{}:
      +c = (F32.floor((px * 2.0 : F32)) + F32.floor((pz * 2.0 : F32)) : F32)
      +v = (sel(~F32, F32.is_eq((c - 2.0 * F32.floor((c * 0.5 : F32)) : F32), 1.0), 0.25, 0.7) * f : F32)
      Path.done(i, x, y, (ar + v : F32), (ag + v : F32), (ab + v : F32), n, seed, acc)
    case False{} False{}:
      +s1 = Rng.next(seed)
      +s2 = Rng.next(s1)
      +mat = (col / 16777216 : U32)
      Path.base(Mats.at(mats, U32.is_eq(((mat / 128 : U32) .&. 1 : U32), 1), (mat .&. 255 : U32), uv, Rng.unit(s1), Rng.unit(s2)), col, f, i, x, y, ar, ag, ab, n, s2, acc)

def Path.tint(h: Hit, +mats: Mats, +tp: F32, +i: U32, +x: U32, +y: U32, +ox: F32, +oz: F32, +dx: F32, +dy: F32, +dz: F32, +ar: F32, +ag: F32, +ab: F32, +n: U32, +seed: U32, acc: PList) -> PList:
  Hit{+t, nx, ny, nz, col, uv, _, _, _} = h
  Path.paint((t >= 1000000000.0 : F32), F32.is_eq(t, tp), mats, col, uv, Path.face(nx, ny, nz, dx, dy, dz), (ox + t * dx : F32), (oz + t * dz : F32), i, x, y, ar, ag, ab, n, seed, acc)

def Path.look(+mode: U32, +scene: Bvh, +mats: Mats, +lights: Lights, +i: U32, +x: U32, +y: U32, +ox: F32, +oy: F32, +oz: F32, +dx: F32, +dy: F32, +dz: F32, +ar: F32, +ag: F32, +ab: F32, +n: U32, +seed: U32, +yp: F32, +pt: Portal, +render: Render, acc: PList) -> PList:
  match mode:
    case 0:
      Path.trace(scene, mats, lights, i, x, y, ox, oy, oz, dx, dy, dz, 1.0, 1.0, 1.0, 1.0, ar, ag, ab, n, 0, seed, yp, pt, render, acc)
    case 1:
      +tp = sel(~F32, ((dy < 0.0) && (oy > yp) : F32), ((yp - oy) / dy : F32), 1000000000.0)
      Path.flat(Ray.cast(scene, ox, oy, oz, dx, dy, dz, tp, False{}), i, x, y, dx, dy, dz, ar, ag, ab, n, seed, acc)
    case _:
      +tp = sel(~F32, ((dy < 0.0) && (oy > yp) : F32), ((yp - oy) / dy : F32), 1000000000.0)
      Path.tint(Ray.cast(scene, ox, oy, oz, dx, dy, dz, tp, False{}), mats, tp, i, x, y, ox, oz, dx, dy, dz, ar, ag, ab, n, seed, acc)

def Path.cam(v: V3, +scene: Bvh, +mats: Mats, +lights: Lights, +i: U32, +x: U32, +y: U32, cam: Cam, +ar: F32, +ag: F32, +ab: F32, +n: U32, +seed: U32, +yp: F32, +pt: Portal, +render: Render, acc: PList) -> PList:
  V3{+vx, +vy, +vz} = v
  Cam{_, _, _, _, _, _, _, _, _, ex, ey, ez} = cam
  +il = (1.0 / F32.sqrt((vx * vx + vy * vy + vz * vz : F32)) : F32)
  Path.look(Render.mode(render), scene, mats, lights, i, x, y, ex, ey, ez, Ray.nz((vx * il : F32)), Ray.nz((vy * il : F32)), Ray.nz((vz * il : F32)), ar, ag, ab, n, seed, yp, pt, render, acc)

def Path.go(fresh: Bool, +scene: Bvh, +mats: Mats, +lights: Lights, +i: U32, +x: U32, +y: U32, +ox: F32, +oy: F32, +oz: F32, +dx: F32, +dy: F32, +dz: F32, +tr: F32, +tg: F32, +tb: F32, +pd: F32, +ar: F32, +ag: F32, +ab: F32, +n: U32, +depth: U32, +seed: U32, +cam: Cam, +yp: F32, +pt: Portal, +render: Render, +fs: U32, acc: PList) -> PList:
  match fresh:
    case False{}:
      Path.trace(scene, mats, lights, i, x, y, ox, oy, oz, dx, dy, dz, tr, tg, tb, pd, ar, ag, ab, n, depth, seed, yp, pt, render, acc)
    case True{}:
      +s1 = Rng.next((seed .^. (fs * 2654435761) : U32))
      +s2 = Rng.next(s1)
      +wx = ((U32.to_f32(x) + Rng.unit(s1) - 1024.0) * 0.0011 : F32)
      +wy = ((512.0 - U32.to_f32(y) - Rng.unit(s2)) * 0.0011 : F32)
      Path.cam(Cam.world(cam, wx, wy, 1.0), scene, mats, lights, i, x, y, cam, ar, ag, ab, n, Rng.next(s2), yp, pt, render, acc)

def Blk.step(ls: PList, +scene: Bvh, +mats: Mats, +lights: Lights, +cam: Cam, +yp: F32, +pt: Portal, +render: Render, +fs: U32, acc: PList) -> PList:
  match ls:
    case PNil{}:
      acc
    case PCons{i, x, y, ox, oy, oz, dx, dy, dz, tr, tg, tb, pd, ar, ag, ab, n, depth, seed, next}:
      Blk.step(next, scene, mats, lights, cam, yp, pt, render, fs, Path.go(U32.is_eq(depth, none()), scene, mats, lights, i, x, y, ox, oy, oz, dx, dy, dz, tr, tg, tb, pd, ar, ag, ab, n, depth, seed, cam, yp, pt, render, fs, acc))

def Trace.node(+k: Nat, +scene: Bvh, +mats: Mats, +lights: Lights, +cam: Cam, +yp: F32, +pt: Portal, +render: Render, +fs: U32, old: PT) -> PT:
  match k old:
    case 0n PLeaf{pl}:
      PLeaf{Blk.step(pl, scene, mats, lights, cam, yp, pt, render, fs, PNil{})}
    case 1n+e PQua{oa, ob, oc, od}:
      a b c d = Trace.node(e, scene, mats, lights, cam, yp, pt, render, fs, oa)
        Trace.node(e, scene, mats, lights, cam, yp, pt, render, fs, ob)
        Trace.node(e, scene, mats, lights, cam, yp, pt, render, fs, oc)
        Trace.node(e, scene, mats, lights, cam, yp, pt, render, fs, od)
      PQua{a, b, c, d}
    case _ _:
      PLeaf{PNil{}}

def Init.block(+n: Nat, +x: U32, +y: U32, acc: PList) -> PList:
  match n:
    case 0n:
      acc
    case 1n+m:
      +i = U32.from_nat(m)
      +px = ((x + i % 8) * 331 % 2048 : U32)
      +py = ((y + i / 8) * 197 % 1024 : U32)
      Init.block(m, x, y, Path.fresh(i, px, py, 0.0, 0.0, 0.0, 0, Rng.seed(px, py), acc))

def Init.node(+k: Nat, +x: U32, +y: U32) -> PT:
  match k:
    case 0n:
      PLeaf{Init.block(32n, x, y, PNil{})}
    case 1n+e:
      +x1 = (x + U32.shln(8, e) : U32)
      +y1 = (y + U32.shln(4, e) : U32)
      a b c d = Init.node(e, x, y) Init.node(e, x1, y) Init.node(e, x, y1) Init.node(e, x1, y1)
      PQua{a, b, c, d}

def Reset.block(ls: PList, acc: PList) -> PList:
  match ls:
    case PNil{}:
      acc
    case PCons{i, x, y, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, seed, next}:
      Reset.block(next, Path.fresh(i, x, y, 0.0, 0.0, 0.0, 0, seed, acc))

def Reset.node(+k: Nat, old: PT) -> PT:
  match k old:
    case 0n PLeaf{pl}:
      PLeaf{Reset.block(pl, PNil{})}
    case 1n+e PQua{oa, ob, oc, od}:
      a b c d = Reset.node(e, oa) Reset.node(e, ob) Reset.node(e, oc) Reset.node(e, od)
      PQua{a, b, c, d}
    case _ _:
      PLeaf{PNil{}}

def Reset.show(st: PT) -> PT:
  Reset.node!(8n, st)

def View.tone(+v: F32) -> F32:
  +e = (v * 0.55 : F32)
  F32.sqrt((e / (1.0 + e) : F32))

def View.pix(+ar: F32, +ag: F32, +ab: F32, +n: U32) -> U32:
  +k = (1.0 / U32.to_f32(sel(~U32, U32.is_eq(n, 0), 1, n)) : F32)
  pack(View.tone((ar * k : F32)), View.tone((ag * k : F32)), View.tone((ab * k : F32)))

def Fetch.slot(ps: PList, +i: U32) -> U32:
  match ps:
    case PNil{}:
      0
    case PCons{j, _, _, _, _, _, _, _, _, _, _, _, _, ar, ag, ab, n, _, _, next}:
      sel(~U32, U32.is_eq(j, i), View.pix(ar, ag, ab, n), Fetch.slot(next, i))

def Fetch.go(+k: Nat, +b0: Bool, +b1: Bool, st: PT, +c: U32, +r: U32, +pw: U32, +i: U32) -> U32:
  match k st:
    case 0n PLeaf{ps}:
      Fetch.slot(ps, i)
    case 1n+e PQua{a, b, cc, d}:
      +pw2 = (pw / 2 : U32)
      Fetch.go(e, U32.is_eq((c / pw2 % 2 : U32), 1), U32.is_eq((r / pw2 % 2 : U32), 1), sel(~PT, b1, sel(~PT, b0, d, cc), sel(~PT, b0, b, a)), c, r, pw2, i)
    case _ _:
      0

def Fetch.pix(+root: PT, +px: U32, +py: U32) -> U32:
  +c = (px * 99 % 2048 : U32)
  +r = (py * 525 % 1024 : U32)
  +bx = (c / 8 : U32)
  +by = (r / 4 : U32)
  Fetch.go(8n, U32.is_eq((bx / 128 : U32), 1), U32.is_eq((by / 128 : U32), 1), root, bx, by, 128, (r % 4 * 8 + c % 8 : U32))

def Fetch.q(+root: PT, +x: U32, +y: U32) -> Image:
  Qua{Pix{Fetch.pix(root, x, y)}, Pix{Fetch.pix(root, (x + 1 : U32), y)}, Pix{Fetch.pix(root, x, (y + 1 : U32))}, Pix{Fetch.pix(root, (x + 1 : U32), (y + 1 : U32))}}

type Four is Data:
  Four{a: Image, b: Image, c: Image, d: Image}

def Image.open(old: Image) -> Four:
  match old:
    case Pix{+c}:
      Four{Pix{c}, Pix{c}, Pix{c}, Pix{c}}
    case Qua{a, b, c, d}:
      Four{a, b, c, d}

def View.node(+k: Nat, +x: U32, +y: U32, +root: PT, old: Four) -> Image:
  match k:
    case 0n:
      Qua{Fetch.q(root, x, y), Fetch.q(root, (x + 2 : U32), y), Fetch.q(root, x, (y + 2 : U32)), Fetch.q(root, (x + 2 : U32), (y + 2 : U32))}
    case 1n+e:
      Four{oa, ob, oc, od} = old
      +h = U32.shln(4, e)
      +x1 = (x + h : U32)
      +y1 = (y + h : U32)
      a b c d = View.node(e, x, y, root, Image.open(oa)) View.node(e, x1, y, root, Image.open(ob)) View.node(e, x, y1, root, Image.open(oc)) View.node(e, x1, y1, root, Image.open(od))
      Qua{a, b, c, d}

def Cam.look(+ex: F32, +ey: F32, +ez: F32, +yaw: F32, +pitch: F32) -> Cam:
  Cam.basis(F32.cos(yaw), F32.sin(yaw), F32.cos(pitch), F32.sin(pitch), ex, ey, ez)

def Cam.court() -> Cam:
  Cam.look((0.0 - 0.57 : F32), (0.0 - 0.24 : F32), 0.02, (0.0 - 1.5708 : F32), 0.15)

def Cam.axes(r: Vec3, u: Vec3, f: Vec3, +ex: F32, +ey: F32, +ez: F32) -> Cam:
  Vec3{rx, ry, rz} = r
  Vec3{ux, uy, uz} = u
  Vec3{fx, fy, fz} = f
  Cam{rx, ry, rz, ux, uy, uz, fx, fy, fz, ex, ey, ez}

def Cam.of(+m: Mat4) -> Cam:
  Mat4{a, b, c, _} = m
  Vec4{ax, ay, az, aw} = a
  Vec4{bx, by, bz, bw} = b
  Vec4{cx, cy, cz, cw} = c
  Cam.axes(Vec3.normalize(Vec3{ax, bx, cx}), Vec3.normalize(Vec3{ay, by, cy}), Vec3.normalize(Vec3{az, bz, cz}), aw, bw, cw)

def Trace.bang(cam: Cam, pt: Portal, +scene: Bvh, +mats: Mats, +lights: Lights, +yp: F32, +render: Render, +fs: U32, st: PT) -> Live():
  (Trace.node!(8n, scene, mats, lights, cam, yp, pt, render, fs, st), (scene, (mats, lights)))

def Trace.show(w: World(), +yp: F32, +pt: Portal, +cam: Cam, +render: Render, +fs: U32, st: PT) -> Live():
  (scene, r) = w
  (mats, lights) = r
  Trace.bang(cam, pt, scene, mats, lights, yp, render, fs, st)

def Init.show() -> PT:
  Init.node!(8n, 0, 0)

def View.root(+root: PT, old: Four) -> Image:
  Four{oa, ob, _, _} = old
  a b = View.node(8n, 0, 0, root, Image.open(oa)) View.node(8n, 1024, 0, root, Image.open(ob))
  Qua{a, b, Pix{0}, Pix{0}}

def View.show(+st: PT, old: Image) -> Image & PT:
  (View.root!(st, Image.open(old)), st)

def Scene.ms(+a: Nat, +b: Nat) -> String:
  Nat.show(Nat.sub(b, a)) ++ " ms"

type Raw is Data:
  Raw{ts: Tris, +n: U32, +fit: Fit, flags: List<&2, U32>, +skinned: Bool, +portal: Portal, mesh: Mesh}

def Scene.raw2(r: Loaded, +f: Fit, flags: List<&2, U32>, +skinned: Bool, +portal: Portal) -> Raw:
  Loaded{ts, +n, prims, rest} = r
  Raw{ts, n, f, flags, skinned, portal, Mesh.of(skinned, prims, rest)}

def Scene.raw1(r: Box & (List<&2, U32> & Bool), +pc: Nat, ws: List<&2, U32>) -> Raw:
  match r:
    case (+box, (flags, sk)):
      +skinned = {sk : Bool}
      +f = Fit.of(box)
      Scene.raw2(Load.prims(pc, ws, f, TNil{}, 0, 0, skinned, Nil{}), f, flags, skinned, Portal.of(box, f))

def Scene.raw(ws: List<&2, U32>, +keep: Bool) -> Raw:
  match ws:
    case 1213418818 <> 5 <> +pc <> +rest:
      Scene.raw1(Load.heads(U32.to_nat(pc), rest, Box.empty(), 0, Nil{}, keep), U32.to_nat(pc), rest)
    case _:
      Raw{TNil{}, 0, Fit{0.0, 0.0, 0.0, 1.0, (0.0 - 1.0 : F32)}, Nil{}, False{}, Portal{(0.0 - 1.0 : F32), (0.0 - 1.0 : F32), 1.0, 1.0, 1.0}, Mesh{Nil{}, Nil{}, Nil{}, Nil{}}}

type Asset is Data:
  Asset{ts: Tris, +n: U32, +fit: Fit, +portal: Portal, +skinned: Bool, ms: List<&2, Mats>, ems: List<&2, Em>, mesh: Mesh}

def Asset.texd(raw: Raw, dir: String) -> IO(Asset):
  Raw{ts, +n, +fit, +flags, +skinned, +portal, mesh} = raw
  Mesh{prims, skins, clips, _} = mesh
  +ems = Em.of(flags, Nil{})
  do IO<Asset>:
    ms : List<&2, Mats> <- Mats.load(flags, dir, Nil{})
    IO.pure(Asset, Asset{ts, n, fit, portal, skinned, ms, ems, Mesh{prims, skins, clips, ems}})

def Asset.bytes(r: File & Got(List<&2, U32>), dir: String, +keep: Bool) -> IO(Asset):
  match r:
    case (f, Done{bytes}):
      do IO<Asset>:
        Unit <- File.close(f)
        +t0 : Nat <- IO.now()
        ws : List<&2, U32> = Words.of(bytes)
        +t1 : Nat <- IO.now()
        raw : Raw = Scene.raw(ws, keep)
        +t2 : Nat <- IO.now()
        asset : Asset <- Asset.texd(raw, dir)
        +t3 : Nat <- IO.now()
        Unit <- IO.print("load: words " ++ Scene.ms(t0, t1) ++ ", triangles " ++ Scene.ms(t1, t2) ++ ", textures " ++ Scene.ms(t2, t3))
        IO.pure(Asset, asset)
    case (f, Fail{(code, text)}):
      IO.die(Asset, code, text)

def Asset.sized(r: File & Got(U32), dir: String, +keep: Bool) -> IO(Asset):
  match r:
    case (f, Done{n}):
      do IO<Asset>:
        b : File & Got(List<&2, U32>) <- File.read_bytes(f, n)
        Asset.bytes(b, dir, keep)
    case (f, Fail{(code, text)}):
      IO.die(Asset, code, text)

def Asset.load(+path: String, +keep: Bool) -> IO(Asset):
  do IO<Asset>:
    f : File <- IO.try(File, File.open(path, "r"))
    s : File & Got(U32) <- File.size(f)
    Asset.sized(s, Dir.of(path), keep)

type Obj is Data:
  Obj{built: Built, leaves: List<&2, LS>}

def Obj.of(+ts: Tris) -> Obj:
  Obj{Bvh.build(Bvh.levels(), ts, Tris.count(ts, 0)), Lights.of(ts, Nil{})}

def Rig.forks() -> Nat:
  6n

def Rig.skin(skins: List<&2, Skin>, +i: U32) -> List<&2, Joint>:
  Skin.joints(Maybe.default(&2, Skin, List.get(&2, Skin, skins, U32.to_nat(i)), Skin{Nil{}}))

def Rig.clip(clips: List<&2, Clip>, +i: U32) -> Maybe<&2, Clip>:
  List.get(&2, Clip, clips, U32.to_nat(i))

def Rig.vnone() -> Vert:
  Vert{Vec3.zero(), Vec3.zero(), Vec2{0.0, 0.0}, 0, Vec4{0.0, 0.0, 0.0, 0.0}}

def Rig.corner(v: Vert, +fit: Fit) -> V:
  Vert{p, n, uv, _, _} = v
  Vec3{px, py, pz} = p
  Vec3{nx, ny, nz} = n
  Vec2{u, w} = uv
  V.fit(V{px, py, pz, nx, ny, nz, u, w}, fit)

def Rig.ids(ids: List<&2, U32>, +depth: Nat, +verts: Tree4<Vert>, +fit: Fit, +m: Mat, acc: Tris) -> Tris:
  match ids:
    case i <> j <> k <> rest:
      Rig.ids(rest, depth, verts, fit, m, Tri.of(Rig.corner(Tree4.at(Vert, depth, verts, i, Rig.vnone()), fit), Rig.corner(Tree4.at(Vert, depth, verts, j, Rig.vnone()), fit), Rig.corner(Tree4.at(Vert, depth, verts, k, Rig.vnone()), fit), m, acc))
    case _:
      acc

def Rig.prims(prims: List<&2, Prim>, +fit: Fit, acc: Tris) -> Tris:
  match prims:
    case Nil{}:
      acc
    case Prim{m, _, depth, verts, ids} <> rest:
      Rig.prims(rest, fit, Rig.ids(ids, depth, verts, fit, m, acc))

def Rig.vbox(t: Tree4<Vert>, acc: Box) -> Box:
  match t:
    case T4Nil{}:
      acc
    case T4Leaf{v}:
      Vert{p, _, _, _, _} = v
      Vec3{x, y, z} = p
      Box.add(acc, x, y, z)
    case T4Qua{a, b, c, d}:
      Rig.vbox(d, Rig.vbox(c, Rig.vbox(b, Rig.vbox(a, acc))))

def Rig.pbox(prims: List<&2, Prim>, acc: Box) -> Box:
  match prims:
    case Nil{}:
      acc
    case Prim{_, _, _, verts, _} <> rest:
      Rig.pbox(rest, Rig.vbox(verts, acc))

def Run.one(p: Live(), +yp: F32, +pt: Portal, +cam: Cam, +render: Render, +fs: U32) -> Live():
  (st, w) = p
  Trace.show(w, yp, pt, cam, render, fs, st)

def Run.steps(n: Nat, p: Live(), +yp: F32, +pt: Portal, +cam: Cam, +render: Render, +fs: U32) -> Live():
  match n:
    case 0n:
      p
    case 1n+m:
      Run.steps(m, Run.one(p, yp, pt, cam, render, fs), yp, pt, cam, render, (fs + 1 : U32))

def Run.lit(pc: Live() & Cam, +n: Nat, +yp: F32, +pt: Portal, +render: Render, +fs: U32) -> Live():
  (pb, cam) = pc
  Run.steps(n, pb, yp, pt, cam, render, fs)

def Run.view2(q: Image & PT, w: World()) -> Image & Live():
  (img, st) = q
  (img, (st, w))

def Run.view(p: Live(), old: Image) -> Image & Live():
  (st, w) = p
  Run.view2(View.show(st, old), w)

def Run.fresh(st: PT, bvh: Bvh, mats: Mats, lights: Lights) -> Live():
  (Reset.show(st), (bvh, (mats, lights)))

type Stat is Data:
  Stat{b: Built, ls: LS}

def Stat.of(o: Obj, +ems: List<&2, Em>) -> Stat:
  Obj{b, leaves} = o
  Stat{b, Lights.made(leaves, ems)}

def World.grown(root: Built, sl: LS, dl: LS) -> Bvh & Lights:
  LS{st, +sw} = sl
  LS{dt, dw} = dl
  (Bvh.of(root), LNode{(sw + dw : F32), sw, st, dt})

def World.grow(s: Stat, d: Obj, +ems: List<&2, Em>) -> Bvh & Lights:
  Stat{sb, sl} = s
  Obj{db, dl} = d
  World.grown(Bvh.join(sb, db), sl, Lights.made(dl, ems))

def World.first(stat: Obj, +ems: List<&2, Em>) -> Bvh & Lights:
  World.grow(Stat.of(stat, ems), Obj{Bvh.leaf(TNil{}), Nil{}}, ems)

def World.unjoin(b: Bvh, l: Lights) -> Stat:
  match b l:
    case BNode{lx0, ly0, lz0, lx1, ly1, lz1, _, _, _, _, _, _, sb, _} LNode{_, sw, sl, _}:
      Stat{Built{sb, lx0, ly0, lz0, lx1, ly1, lz1, 0.0}, LS{sl, sw}}
    case _ _:
      Stat{Bvh.leaf(TNil{}), LS{LNil{}, 0.0}}

def World.fresh(st: PT, mats: Mats, bl: Bvh & Lights) -> Live():
  (bvh, lights) = bl
  Run.fresh(st, bvh, mats, lights)

def World.step(pb: Live(), dyn: Obj, +ems: List<&2, Em>) -> Live():
  (st, w) = pb
  (old, r) = w
  (mats, ol) = r
  World.fresh(st, mats, World.grow(World.unjoin(old, ol), dyn, ems))

def Dump.at(+k: Nat, +img: Image, +x: U32, +y: U32, left: Bool, top: Bool) -> U32:
  match k img:
    case _ Pix{c}:
      c
    case 0n Qua{tl, tr, bl, br}:
      0
    case 1n+e Qua{tl, tr, bl, br}:
      match left top:
        case True{} True{}:
          +q = (U32.shln(1, e) / 2 : U32)
          Dump.at(e, tl, x, y, (x < q : U32), (y < q : U32))
        case False{} True{}:
          +h = U32.shln(1, e)
          +q = (h / 2 : U32)
          +x2 = (x - h : U32)
          Dump.at(e, tr, x2, y, (x2 < q : U32), (y < q : U32))
        case True{} False{}:
          +h = U32.shln(1, e)
          +q = (h / 2 : U32)
          +y2 = (y - h : U32)
          Dump.at(e, bl, x, y2, (x < q : U32), (y2 < q : U32))
        case False{} False{}:
          +h = U32.shln(1, e)
          +q = (h / 2 : U32)
          +x2 = (x - h : U32)
          +y2 = (y - h : U32)
          Dump.at(e, br, x2, y2, (x2 < q : U32), (y2 < q : U32))

def Dump.pix(+c: U32) -> String:
  U32.show(((c >> 16n : U32) .&. 255 : U32)) ++ " " ++ U32.show(((c >> 8n : U32) .&. 255 : U32)) ++ " " ++ U32.show((c .&. 255 : U32)) ++ " "

def Dump.row(+n: Nat, +img: Image, +y: U32, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+k:
      +x = U32.from_nat(k)
      Dump.row(k, img, y, Dump.pix(Dump.at(11n, img, x, y, (x < 1024 : U32), (y < 1024 : U32))) ++ acc)

def Dump.got(w: File & Got(Unit)) -> IO(File):
  (f, _) = w
  IO.pure(File, f)

def Dump.text(+n: Nat, +img: Image, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+k:
      Dump.text(k, img, Dump.row(2048n, img, U32.from_nat(k), "\n" ++ acc))

def Dump.take(+img: Image) -> String & Image:
  ("P3\n2048 1024\n255\n" ++ Dump.text(1024n, img, ""), img)

def Dump.write(path: Got(String), text: String) -> IO(Unit):
  match path:
    case Fail{_}:
      IO.pure(Unit, Unit{})
    case Done{name}:
      do IO<Unit>:
        f : File <- IO.try(File, File.open(name, "w"))
        w : File & Got(Unit) <- File.write(f, text)
        f2 : File <- Dump.got(w)
        File.close(f2)

def Film.name(+prefix: String, +i: U32) -> Got(String):
  Done{prefix ++ U32.show(i) ++ ".ppm"}

def Film.write(r: String & Image, pb: Live(), +prefix: String, +i: U32, +t0: Nat, +t1: Nat, +t2: Nat, rest: (Image & Live()) -> IO(Unit)) -> IO(Unit):
  (text, img) = r
  do IO<Unit>:
    Unit <- Dump.write(Film.name(prefix, i), text)
    +t3 : Nat <- IO.now()
    Unit <- IO.print("frame " ++ U32.show(i) ++ "  pose " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms  trace " ++ Nat.show(Nat.sub(t2, t1)) ++ " ms  dump " ++ Nat.show(Nat.sub(t3, t2)) ++ " ms")
    rest((img, pb))

def Film.dump(drawn: Image & Live(), +prefix: String, +i: U32, +t0: Nat, +t1: Nat, rest: (Image & Live()) -> IO(Unit)) -> IO(Unit):
  (img, pb) = drawn
  do IO<Unit>:
    +t2 : Nat <- IO.now()
    Film.write(Dump.take(img), pb, prefix, i, t0, t1, t2, rest)

def Env.text(r: Got(String), default: String) -> String:
  Result.default(&1, &1, U32 & String, String, r, default)

def Env.read(r: Got(String), +default: U32) -> U32:
  Maybe.default(&2, U32, U32.read(Env.text(r, "")), default)

def Env.f32(s: String) -> F32:
  Maybe.default(&2, F32, F32.read(s), 0.0)

def Env.num(name: String, +default: U32) -> IO(U32):
  IO.bind(Got(String), U32, IO.get_env(name), r => IO.pure(U32, Env.read(r, default)))

def Env.cam2(parts: List<&2, String>) -> Cam:
  match parts:
    case a <> b <> c <> d <> e <> _:
      Cam.look(Env.f32(a), Env.f32(b), Env.f32(c), Env.f32(d), Env.f32(e))
    case _:
      Cam.court()

def Env.cam(r: Got(String)) -> Cam:
  match r:
    case Fail{_}:
      Cam.court()
    case Done{text}:
      Env.cam2(String.split(text, ','))

type Act is Data:
  Play{+clip: U32}
  Slide{+vx: F32, +vy: F32, +vz: F32}
  Spin{+rate: F32}

type Item is Data:
  Item{path: String, +parent: U32, +place: Mat4, acts: List<&2, Act>}
  Eye{+parent: U32, +place: Mat4, acts: List<&2, Act>}

type Cut is Data:
  Cut{+eye: U32, +start: U32}

type Inst is Data:
  Inst{+node: U32, +parent: U32, +place: Mat4, acts: List<&2, Act>, joints: List<&2, Joint>, clip: Maybe<&2, Clip>, prims: List<&2, Prim>, +live: Bool}

type Bake is Data:
  Bake{+node: U32, +base: U32, ts: Tris}

type Cast is Data:
  Cast{insts: List<&2, Inst>, bakes: List<&2, Bake>, ms: List<&2, Mats>, ems: List<&2, Em>, nodes: List<&2, U32>, +n: U32, +base: U32, +yp: F32, +pt: Portal, eyes: List<&2, U32>}

def Act.mat(a: Act, +frame: U32) -> Mat4:
  match a:
    case Play{_}:
      Mat4.id()
    case Slide{vx, vy, vz}:
      Mat4.move((vx * U32.to_f32(frame) : F32), (vy * U32.to_f32(frame) : F32), (vz * U32.to_f32(frame) : F32))
    case Spin{rate}:
      Mat4.turn_y((rate * U32.to_f32(frame) : F32))

def Acts.mat(acts: List<&2, Act>, +frame: U32) -> Mat4:
  match acts:
    case Nil{}:
      Mat4.id()
    case a <> rest:
      Mat4.mul(Act.mat(a, frame), Acts.mat(rest, frame))

def Acts.clip(acts: List<&2, Act>) -> U32:
  match acts:
    case Nil{}:
      none()
    case Play{clip} <> _:
      clip
    case _ <> rest:
      Acts.clip(rest)

def Graph.at(+t: Tree4<Mat4>, +i: U32) -> Mat4:
  Tree4.at(Mat4, 6n, t, i, Mat4.id())

def Graph.up(root: Bool, +t: Tree4<Mat4>, +parent: U32) -> Mat4:
  match root:
    case True{}:
      Mat4.id()
    case False{}:
      Graph.at(t, parent)

def Graph.put(+t: Tree4<Mat4>, +i: U32, +parent: U32, local: Mat4) -> Tree4<Mat4>:
  Tree4.set(Mat4, 6n, t, i, Mat4.mul(Graph.up(U32.is_eq(parent, none()), t, parent), local))

def Graph.joints(joints: List<&2, Joint>, pose: List<&2, Trs>, +inst: U32, +at: U32, +k: U32, +t: Tree4<Mat4>) -> Tree4<Mat4>:
  match joints pose:
    case Joint{_, +parent, pre, _, _} <> js p <> ps:
      Graph.joints(js, ps, inst, at, (k + 1 : U32), Graph.put(t, (at + k : U32), sel(~U32, U32.is_eq(parent, none()), inst, (at + parent : U32)), Mat4.mul(pre, Trs.to_mat4(p))))
    case _ _:
      t

def Inst.pose(mc: Maybe<&2, Clip>, joints: List<&2, Joint>, +frame: U32, +fps: U32) -> List<&2, Trs>:
  match mc:
    case None{}:
      Pose.rest(joints)
    case Some{+clip}:
      Clip.sample(clip, frame, fps)

def Graph.eval(insts: List<&2, Inst>, +frame: U32, +fps: U32, +t: Tree4<Mat4>) -> Tree4<Mat4>:
  match insts:
    case Nil{}:
      t
    case Inst{+node, parent, place, acts, +joints, clip, _, _} <> rest:
      Graph.eval(rest, frame, fps, Graph.joints(joints, Inst.pose(clip, joints, frame, fps), node, (node + 1 : U32), 0, Graph.put(t, node, parent, Mat4.mul(Acts.mat(acts, frame), place))))

def Bind.pal(joints: List<&2, Joint>, +worlds: Tree4<Mat4>, +at: U32, +k: U32, acc: Tree4<Mat4>) -> Tree4<Mat4>:
  match joints:
    case Nil{}:
      acc
    case Joint{_, _, _, _, bind} <> js:
      Bind.pal(js, worlds, at, (k + 1 : U32), Pal.set(acc, k, Mat4.mul(Graph.at(worlds, (at + k : U32)), bind)))

def Inst.tris(+node: U32, joints: List<&2, Joint>, prims: List<&2, Prim>, +worlds: Tree4<Mat4>, acc: Tris) -> Tris:
  Rig.prims(Skin.prims(Rig.forks(), Bind.pal(joints, worlds, (node + 1 : U32), 0, T4Nil{}), Graph.at(worlds, node), prims), Fit.id(), acc)

def Stage.part(take: Bool, +node: U32, joints: List<&2, Joint>, prims: List<&2, Prim>, +worlds: Tree4<Mat4>, acc: Tris) -> Tris:
  match take:
    case True{}:
      Inst.tris(node, joints, prims, worlds, acc)
    case False{}:
      acc

def Stage.tris(+want: Bool, insts: List<&2, Inst>, +worlds: Tree4<Mat4>, acc: Tris) -> Tris:
  match insts:
    case Nil{}:
      acc
    case Inst{node, _, _, _, joints, _, prims, +live} <> rest:
      Stage.tris(want, rest, worlds, Stage.part(((live && want) || (Bool.not(live) && Bool.not(want))), node, joints, prims, worlds, acc))

def Stage.bakes(bakes: List<&2, Bake>, +worlds: Tree4<Mat4>, acc: Tris) -> Tris:
  match bakes:
    case Nil{}:
      acc
    case Bake{node, base, ts} <> rest:
      Stage.bakes(rest, worlds, Tris.xf(Graph.at(worlds, node), base, ts, acc))

def Stage.rest(+insts: List<&2, Inst>, bakes: List<&2, Bake>, +worlds: Tree4<Mat4>) -> Obj:
  Obj.of(Stage.tris(False{}, insts, worlds, Stage.bakes(bakes, worlds, TNil{})))

def Stage.still(+insts: List<&2, Inst>, bakes: List<&2, Bake>, +fps: U32) -> Obj:
  Stage.rest(insts, bakes, Graph.eval(insts, 0, fps, T4Nil{}))

def Stage.worlds(+insts: List<&2, Inst>, +frame: U32, +fps: U32) -> Tree4<Mat4>:
  Graph.eval(insts, frame, fps, T4Nil{})

def Stage.pose(+insts: List<&2, Inst>, +worlds: Tree4<Mat4>) -> Obj:
  Obj.of(Stage.tris(True{}, insts, worlds, TNil{}))

def Cut.at(cuts: List<&2, Cut>, +frame: U32, +cur: U32) -> U32:
  match cuts:
    case Nil{}:
      cur
    case Cut{eye, start} <> rest:
      Cut.at(rest, frame, sel(~U32, (start <= frame : U32), eye, cur))

def Stage.eye(m: Maybe<&2, U32>, +worlds: Tree4<Mat4>, +cam: Cam) -> Cam:
  match m:
    case None{}:
      cam
    case Some{node}:
      Cam.of(Graph.at(worlds, node))

def Stage.cam(+worlds: Tree4<Mat4>, +eyes: List<&2, U32>, +cuts: List<&2, Cut>, +frame: U32, +cam: Cam) -> Cam:
  Stage.eye(List.get(&2, U32, eyes, U32.to_nat(Cut.at(cuts, frame, 0))), worlds, cam)

def Prims.shift(prims: List<&2, Prim>, +base: U32) -> List<&2, Prim>:
  match prims:
    case Nil{}:
      Nil{}
    case Prim{mat, skin, depth, verts, ids} <> rest:
      Mat{col, metal, rough, le} = mat
      Prim{Mat{(col + base * 16777216 : U32), metal, rough, le}, skin, depth, verts, ids} <> Prims.shift(rest, base)

def Joints.any(js: List<&2, Joint>) -> Bool:
  match js:
    case Nil{}:
      False{}
    case _:
      True{}

def Inst.skin(skins: List<&2, Skin>, mc: Maybe<&2, Clip>) -> List<&2, Joint>:
  match mc:
    case None{}:
      Rig.skin(skins, 0)
    case Some{clip}:
      Clip{_, +sk, _, _, _, _} = clip
      Rig.skin(skins, sk)

def Inst.fit(skinned: Bool, +joints: List<&2, Joint>, clip: Maybe<&2, Clip>, prims: List<&2, Prim>, +fps: U32, fit: Fit) -> Fit:
  match skinned:
    case False{}:
      fit
    case True{}:
      Fit.of(Rig.pbox(Skin.prims(Rig.forks(), Bind.pal(joints, Graph.joints(joints, Inst.pose(clip, joints, 0, fps), none(), 1, 0, T4Nil{}), 1, 0, T4Nil{}), Mat4.id(), prims), Box.empty()))

def Item.live(acts: List<&2, Act>, +parent: U32) -> Bool:
  match acts:
    case Nil{}:
      Bool.not(U32.is_eq(parent, none()))
    case _:
      True{}

def Item.node(nodes: List<&2, U32>, +parent: U32) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, nodes, U32.to_nat(parent)), none())

def Cast.none() -> Cast:
  Cast{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}, 0, 0, (0.0 - 1.0 : F32), Portal{(0.0 - 1.0 : F32), (0.0 - 1.0 : F32), 1.0, 1.0, 1.0}, Nil{}}

def Cast.bake(c: Cast, ts: Tris, +parent: U32, +place: Mat4) -> Cast:
  Cast{insts, bakes, ms, ems, +nodes, +n, +base, yp, pt, eyes} = c
  Cast{Inst{n, Item.node(nodes, parent), place, Nil{}, Nil{}, None{}, Nil{}, False{}} <> insts, Bake{n, base, ts} <> bakes, ms, ems, List.append(&2, U32, nodes, n <> Nil{}), (n + 1 : U32), base, yp, pt, eyes}

def Cast.keep(c: Cast, +parent: U32, +place: Mat4, acts: List<&2, Act>, +joints: List<&2, Joint>, clip: Maybe<&2, Clip>, prims: List<&2, Prim>, +fit: Fit, +live: Bool) -> Cast:
  Cast{insts, bakes, ms, ems, +nodes, +n, +base, yp, pt, eyes} = c
  Cast{Inst{n, Item.node(nodes, parent), Mat4.mul(place, Fit.mat(fit)), acts, joints, clip, Prims.shift(prims, base), live} <> insts, bakes, ms, ems, List.append(&2, U32, nodes, n <> Nil{}), (n + 1 + U32.from_nat(List.length(&2, Joint, joints)) : U32), base, yp, pt, eyes}

def Cast.item(c: Cast, ts: Tris, prims: List<&2, Prim>, +joints: List<&2, Joint>, +clip: Maybe<&2, Clip>, +fit: Fit, +parent: U32, +place: Mat4, acts: List<&2, Act>, +live: Bool, +fps: U32) -> Cast:
  match prims:
    case Nil{}:
      Cast.bake(c, ts, parent, place)
    case +p <> +ps:
      Cast.keep(c, parent, place, acts, joints, clip, p <> ps, Inst.fit(Joints.any(joints), joints, clip, p <> ps, fps, fit), live)

def Cast.mats(c: Cast, +ms2: List<&2, Mats>, ems2: List<&2, Em>, +fit: Fit, +portal: Portal) -> Cast:
  Cast{insts, bakes, ms, ems, nodes, n, +base, +yp, +pt, eyes} = c
  Cast{insts, bakes, List.append(&2, Mats, ms, ms2), List.append(&2, Em, ems, ems2), nodes, n, (base + U32.from_nat(List.length(&2, Mats, ms2)) : U32), sel(~F32, U32.is_eq(base, 0), Fit.floor(fit), yp), sel(~Portal, U32.is_eq(base, 0), portal, pt), eyes}

def Cast.add(c: Cast, a: Asset, +parent: U32, +place: Mat4, +acts: List<&2, Act>, +fps: U32) -> Cast:
  Asset{ts, _, +fit, +portal, _, ms, ems, mesh} = a
  Mesh{prims, skins, clips, _} = mesh
  +clip = Rig.clip(clips, Acts.clip(acts))
  Cast.mats(Cast.item(c, ts, prims, Inst.skin(skins, clip), clip, fit, parent, place, acts, Item.live(acts, parent), fps), ms, ems, fit, portal)

def Cast.eye(c: Cast, +parent: U32, +place: Mat4, acts: List<&2, Act>) -> Cast:
  Cast{insts, bakes, ms, ems, +nodes, +n, base, yp, pt, eyes} = c
  Cast{Inst{n, Item.node(nodes, parent), place, acts, Nil{}, None{}, Nil{}, True{}} <> insts, bakes, ms, ems, List.append(&2, U32, nodes, n <> Nil{}), (n + 1 : U32), base, yp, pt, List.append(&2, U32, eyes, n <> Nil{})}

def Stage.load(items: List<&2, Item>, +fps: U32, c: Cast) -> IO(Cast):
  match items:
    case Nil{}:
      IO.pure(Cast, c)
    case Item{+path, +parent, +place, +acts} <> rest:
      do IO<Cast>:
        a : Asset <- Asset.load(path, Item.live(acts, parent))
        Stage.load(rest, fps, Cast.add(c, a, parent, place, acts, fps))
    case Eye{+parent, +place, +acts} <> rest:
      Stage.load(rest, fps, Cast.eye(c, parent, place, acts))

type Tick is Data:
  Tick{+insts: List<&2, Inst>, +ems: List<&2, Em>, +fps: U32, +eyes: List<&2, U32>, +cuts: List<&2, Cut>, +cam: Cam}

def Tick.world(+k: Tick, +frame: U32, pb: Live()) -> IO(Live() & Cam):
  match k:
    case Tick{insts, ems, fps, eyes, cuts, cam}:
      +worlds = Stage.worlds(insts, frame, fps)
      do IO<Live() & Cam>:
        dyn : Obj = Stage.pose(insts, worlds)
        now : Nat <- IO.now()
        IO.pure(Live() & Cam, (World.step(pb, dyn, ems), Stage.cam(worlds, eyes, cuts, frame, cam)))

def Film.step(+i: U32, +k: Tick, +yp: F32, +pt: Portal, +render: Render, +ns: Nat, +prefix: String, last: Image & Live(), rest: (Image & Live()) -> IO(Unit)) -> IO(Unit):
  (old, pb) = last
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    pc : Live() & Cam <- Tick.world(k, i, pb)
    +t1 : Nat <- IO.now()
    p2 : Live() <- IO.pure(Live(), Run.lit(pc, ns, yp, pt, render, (i * U32.from_nat(ns) : U32)))
    drawn : Image & Live() <- IO.pure(Image & Live(), Run.view(p2, old))
    Film.dump(drawn, prefix, i, t0, t1, rest)

def Film.loop(n: Nat, +i: U32, +k: Tick, +yp: F32, +pt: Portal, +render: Render, +ns: Nat, +prefix: String, last: Image & Live()) -> IO(Unit):
  match n:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+j:
      Film.step(i, k, yp, pt, render, ns, prefix, last, l => Film.loop(j, (i + 1 : U32), k, yp, pt, render, ns, prefix, l))

def Film.run(+n: Nat, scene: Bvh, mats: Mats, lights: Lights, +yp: F32, +pt: Portal, +render: Render, +ns: Nat, +k: Tick, +prefix: String) -> IO(Unit):
  do IO<Unit>:
    st : PT = Init.show()
    Film.loop(n, 0, k, yp, pt, render, ns, prefix, (Pix{0}, (st, (scene, (mats, lights)))))

type Stage is Data:
  Stage{bvh: Bvh, lights: Lights, insts: List<&2, Inst>, mats: Mats, ems: List<&2, Em>, eyes: List<&2, U32>, cuts: List<&2, Cut>, +yp: F32, +pt: Portal, +n: U32}

def Stage.first(bl: Bvh & Lights, insts: List<&2, Inst>, mats: Mats, ems: List<&2, Em>, eyes: List<&2, U32>, cuts: List<&2, Cut>, +yp: F32, +pt: Portal, +n: U32) -> IO(Stage):
  (bvh, lights) = bl
  IO.pure(Stage, Stage{bvh, lights, insts, mats, ems, eyes, cuts, yp, pt, n})

def Stage.made(c: Cast, cuts: List<&2, Cut>, +fps: U32) -> IO(Stage):
  Cast{insts, bakes, +ms, +ems, _, +n, _, +yp, +pt, +eyes} = c
  +live = List.reverse(&2, Inst, insts)
  do IO<Stage>:
    +t0 : Nat <- IO.now()
    stat : Obj = Stage.still(live, bakes, fps)
    +t1 : Nat <- IO.now()
    Unit <- IO.print("stage: " ++ U32.show(n) ++ " nodes, static built in " ++ Scene.ms(t0, t1))
    Stage.first(World.first(stat, ems), live, Mats.tree(ms), ems, eyes, cuts, yp, pt, n)

def Stage.build(items: List<&2, Item>, cuts: List<&2, Cut>, +fps: U32) -> IO(Stage):
  do IO<Stage>:
    c : Cast <- Stage.load(items, fps, Cast.none())
    Stage.made(c, cuts, fps)

type Shot is Data:
  Shot{+frames: U32, +steps: U32, +fps: U32, +bounces: U32, +mode: U32, +cam: Cam, prefix: String}

def Film.shot(s: Stage, +frames: U32, +steps: U32, +fps: U32, +bounces: U32, +mode: U32, +cam: Cam, prefix: String) -> IO(Unit):
  Stage{bvh, lights, insts, mats, ems, eyes, cuts, yp, pt, _} = s
  Film.run(U32.to_nat(frames), bvh, mats, lights, yp, pt, Render{bounces, mode}, U32.to_nat(steps), Tick{insts, ems, fps, eyes, cuts, cam}, prefix)

def Film.stage(items: List<&2, Item>, cuts: List<&2, Cut>, shot: Shot) -> IO(Unit):
  Shot{frames, steps, +fps, bounces, mode, cam, prefix} = shot
  do IO<Unit>:
    s : Stage <- Stage.build(items, cuts, fps)
    Film.shot(s, frames, steps, fps, bounces, mode, cam, prefix)
