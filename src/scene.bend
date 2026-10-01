import Base
import ./core.bend as C

def Fire.mesh() -> String:
  "assets/imported/sponza-png/sponza-png.mesh"

def Fire.cuts() -> List<&2, C.Cut>:
  Nil{}

type Fire is Data:
  Fire{+insts: List<&2, C.Inst>, +ems: List<&2, C.Em>, +fps: U32, +eyes: List<&2, U32>, +cuts: List<&2, C.Cut>, +cam: C.Cam, +yp: F32, +pt: C.Portal, +render: C.Render, +ns: Nat, +mat: U32, +prefix: String, +spots: List<&2, C.Vec3>}

def Fire.at(+fit: C.Fit, +bx: F32, +by: F32, +bz: F32) -> C.Vec3:
  C.Fit{cx, cy, cz, +s, _} = fit
  C.Vec3{((bx - cx) * s : F32), ((bz - cy) * s : F32), ((0.0 - by - cz) * s : F32)}

def Fire.spots(+fit: C.Fit) -> List<&2, C.Vec3>:
  Fire.at(fit, 3.898, (0.0 - 1.14 : F32), 0.991) <>
  Fire.at(fit, (0.0 - 4.977 : F32), (0.0 - 1.14 : F32), 0.991) <>
  Fire.at(fit, (0.0 - 4.977 : F32), 1.758, 0.991) <>
  Fire.at(fit, 3.898, 1.758, 0.991) <>
  Nil{}

def Fire.count() -> Nat:
  200n

def Fire.leaf(+er: F32, +eg: F32, +eb: F32) -> C.Mats:
  C.MtLeaf{1, C.TFlat{16777215}, 1, C.TFlat{16777215}, 1, C.TFlat{8421631}, 0.0, 1.0, 1.0, er, eg, eb}

def Fire.em(+er: F32, +eg: F32, +eb: F32) -> C.Em:
  C.Em{C.Em.lum(er, eg, eb), er, eg, eb}

def Fire.cast(c: C.Cast) -> C.Cast & U32:
  C.Cast{insts, bakes, ms, ems, nodes, n, +base, yp, pt, eyes} = c
  (C.Cast{insts, bakes, List.append(&2, C.Mats, ms, Fire.leaf(900.0, 540.0, 180.0) <> Fire.leaf(480.0, 150.0, 24.0) <> Fire.leaf(120.0, 24.0, 6.0) <> Nil{}), List.append(&2, C.Em, ems, Fire.em(900.0, 540.0, 180.0) <> Fire.em(480.0, 150.0, 24.0) <> Fire.em(120.0, 24.0, 6.0) <> Nil{}), nodes, n, (base + 3 : U32), yp, pt, eyes}, base)

def Fire.glow(+k: U32) -> F32:
  match k:
    case 0:
      C.Em.lum(900.0, 540.0, 180.0)
    case 1:
      C.Em.lum(480.0, 150.0, 24.0)
    case _:
      C.Em.lum(120.0, 24.0, 6.0)

def Fire.tier(hot: Bool, warm: Bool) -> U32:
  match hot warm:
    case True{} _:
      0
    case False{} True{}:
      1
    case False{} False{}:
      2

def Fire.mix(+h: U32) -> U32:
  +h1 = ((h .^. (h / 65536)) * 2246822507 : U32)
  +h2 = ((h1 .^. (h1 / 8192)) * 3266489909 : U32)
  (h2 .^. (h2 / 65536) : U32)

def Fire.hash(+j: U32, +k: U32) -> F32:
  C.Rng.unit(Fire.mix((j * 2654435761 + k * 2246822519 : U32)))

def Fire.frac(+x: F32) -> F32:
  (x - F32.floor(x) : F32)

def Fire.v(+x: F32, +y: F32, +z: F32, +nx: F32, +ny: F32, +nz: F32) -> C.V:
  C.V{x, y, z, nx, ny, nz, 0.0, 0.0}

def Fire.mat(+mat: U32, +le: F32) -> C.Mat:
  C.Mat{(16777215 + mat * 16777216 : U32), 0.0, 1.0, le}

type Wind is Data:
  Wind{+phase: F32, +f1: F32, +f2: F32, +amp: F32}

def Wind.of(+id: U32) -> Wind:
  Wind{(6.2831853 * Fire.hash(id, 9) : F32), (1.0 + 1.6 * Fire.hash(id, 10) : F32), (2.5 + 2.5 * Fire.hash(id, 11) : F32), (0.005 + 0.005 * Fire.hash(id, 12) : F32)}

def Fire.put(+j: U32, +t: F32, +w: Wind, +base: U32, +ox: F32, +oy: F32, +oz: F32, acc: C.Tris) -> C.Tris:
  Wind{phase, +f1, +f2, +amp} = w
  +a = Fire.frac((t * 1.2 + Fire.hash(j, 1) : F32))
  +ang = (6.2831853 * Fire.hash(j, 2) : F32)
  +rad = (0.014 * F32.sqrt(Fire.hash(j, 3)) * (1.0 - 0.7 * a) : F32)
  +sw = (0.003 * a * F32.sin((9.0 * a + 6.2831853 * Fire.hash(j, 4) : F32)) : F32)
  +tw = (f1 * t + phase : F32)
  +mx = (a * amp * (F32.sin((tw - 6.5 * a : F32)) + 0.5 * F32.sin((f2 * t - 11.0 * a + 1.7 : F32))) : F32)
  +mz = (a * amp * (F32.cos((0.8 * tw - 5.5 * a : F32)) + 0.5 * F32.sin((0.9 * f2 * t - 9.0 * a + 0.6 : F32))) : F32)
  +x = (ox + rad * F32.cos(ang) + sw + mx : F32)
  +y = (oy + 0.04 * a * (0.7 + 0.6 * Fire.hash(j, 5)) : F32)
  +z = (oz + rad * F32.sin(ang) + mz : F32)
  +s = (0.0004 + 0.0007 * (1.0 - a) : F32)
  +k = Fire.tier((a < 0.3 : F32), (a < 0.65 : F32))
  +m = Fire.mat((base + k : U32), Fire.glow(k))
  C.Tri.of(Fire.v((x - s : F32), y, z, 0.0, 0.0, 1.0), Fire.v((x + s : F32), y, z, 0.0, 0.0, 1.0), Fire.v(x, (y + 2.0 * s : F32), z, 0.0, 0.0, 1.0), m,
    C.Tri.of(Fire.v(x, y, (z - s : F32), 1.0, 0.0, 0.0), Fire.v(x, y, (z + s : F32), 1.0, 0.0, 0.0), Fire.v(x, (y + 2.0 * s : F32), z, 1.0, 0.0, 0.0), m, acc))

def Fire.tris(+n: Nat, +t: F32, +w: Wind, +base: U32, +id: U32, +ox: F32, +oy: F32, +oz: F32, acc: C.Tris) -> C.Tris:
  match n:
    case 0n:
      acc
    case 1n+m:
      Fire.tris(m, t, w, base, id, ox, oy, oz, Fire.put((id + U32.from_nat(m) : U32), t, w, base, ox, oy, oz, acc))

def Fire.all(spots: List<&2, C.Vec3>, +t: F32, +base: U32, +id: U32, acc: C.Tris) -> C.Tris:
  match spots:
    case Nil{}:
      acc
    case C.Vec3{ox, oy, oz} <> rest:
      Fire.all(rest, t, base, (id + 4096 : U32), Fire.tris(Fire.count(), t, Wind.of(id), base, id, ox, oy, oz, acc))

def Fire.ns(f: Fire) -> Nat:
  Fire{_, _, _, _, _, _, _, _, _, ns, _, _, _} = f
  ns

def Fire.yp(f: Fire) -> F32:
  Fire{_, _, _, _, _, _, yp, _, _, _, _, _, _} = f
  yp

def Fire.pt(f: Fire) -> C.Portal:
  Fire{_, _, _, _, _, _, _, pt, _, _, _, _, _} = f
  pt

def Fire.render(f: Fire) -> C.Render:
  Fire{_, _, _, _, _, _, _, _, render, _, _, _, _} = f
  render

def Fire.prefix(f: Fire) -> String:
  Fire{_, _, _, _, _, _, _, _, _, _, _, prefix, _} = f
  prefix

def Fire.world(+f: Fire, +i: U32, pb: C.Live()) -> IO(C.Live() & C.Cam):
  match f:
    case Fire{insts, ems, fps, eyes, cuts, cam, _, _, _, _, mat, _, spots}:
      +worlds = C.Stage.worlds(insts, i, fps)
      +t = (U32.to_f32(i) / U32.to_f32(fps) : F32)
      do IO<C.Live() & C.Cam>:
        dyn : C.Obj = C.Obj.of(C.Stage.tris(True{}, insts, worlds, Fire.all(spots, t, mat, 0, C.TNil{})))
        now : Nat <- IO.now()
        IO.pure(C.Live() & C.Cam, (C.World.step(pb, dyn, ems), C.Stage.cam(worlds, eyes, cuts, i, cam)))

def Fire.ran(r: C.Got(U32 & (String & String))) -> IO(Unit):
  match r:
    case Done{(status, (out, err))}:
      IO.write(err)
    case Fail{(code, msg)}:
      IO.die(Unit, code, "ppm2png: " ++ msg)

def Fire.write(r: String & Image, pb: C.Live(), +prefix: String, +i: U32, +t0: Nat, +t1: Nat, +t2: Nat, rest: (Image & C.Live()) -> IO(Unit)) -> IO(Unit):
  (text, img) = r
  do IO<Unit>:
    ran : C.Got(U32 & (String & String)) <- Process.run("node", ["tools/ppm2png.js", prefix ++ U32.show(i) ++ ".png"], text, 65536, 60000)
    Unit <- Fire.ran(ran)
    +t3 : Nat <- IO.now()
    Unit <- IO.print("frame " ++ U32.show(i) ++ "  pose " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms  trace " ++ Nat.show(Nat.sub(t2, t1)) ++ " ms  png " ++ Nat.show(Nat.sub(t3, t2)) ++ " ms")
    rest((img, pb))

def Fire.dump(drawn: Image & C.Live(), +prefix: String, +i: U32, +t0: Nat, +t1: Nat, rest: (Image & C.Live()) -> IO(Unit)) -> IO(Unit):
  (img, pb) = drawn
  do IO<Unit>:
    +t2 : Nat <- IO.now()
    Fire.write(C.Dump.take(img), pb, prefix, i, t0, t1, t2, rest)

def Fire.step(+i: U32, +f: Fire, last: Image & C.Live(), rest: (Image & C.Live()) -> IO(Unit)) -> IO(Unit):
  (old, pb) = last
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    pc : C.Live() & C.Cam <- Fire.world(f, i, pb)
    +t1 : Nat <- IO.now()
    p2 : C.Live() <- IO.pure(C.Live(), C.Run.lit(pc, Fire.ns(f), Fire.yp(f), Fire.pt(f), Fire.render(f), (i * U32.from_nat(Fire.ns(f)) : U32)))
    drawn : Image & C.Live() <- IO.pure(Image & C.Live(), C.Run.view(p2, old))
    Fire.dump(drawn, Fire.prefix(f), i, t0, t1, rest)

def Fire.loop(n: Nat, +i: U32, +f: Fire, last: Image & C.Live()) -> IO(Unit):
  match n:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+j:
      Fire.step(i, f, last, l => Fire.loop(j, (i + 1 : U32), f, l))

def Fire.run(s: C.Stage, +base: U32, +fps: U32, +cam: C.Cam, +render: C.Render, +ns: Nat, +frames: U32, +prefix: String, spots: List<&2, C.Vec3>) -> IO(Unit):
  C.Stage{bvh, lights, insts, mats, ems, eyes, cuts, yp, pt, _} = s
  do IO<Unit>:
    st : C.PT = C.Init.show()
    Fire.loop(U32.to_nat(frames), 0, Fire{insts, ems, fps, eyes, cuts, cam, yp, pt, render, ns, base, prefix, spots}, (Pix{0}, (st, (bvh, (mats, lights)))))

def Fire.fit(a: C.Asset) -> C.Fit:
  C.Asset{_, _, fit, _, _, _, _, _} = a
  fit

def Fire.built(cb: C.Cast & U32, +fps: U32, spots: List<&2, C.Vec3>) -> IO(C.Stage & (U32 & List<&2, C.Vec3>)):
  (c, base) = cb
  do IO<C.Stage & (U32 & List<&2, C.Vec3>)>:
    s : C.Stage <- C.Stage.made(c, Fire.cuts(), fps)
    IO.pure(C.Stage & (U32 & List<&2, C.Vec3>), (s, (base, spots)))

def Fire.setup(+fps: U32) -> IO(C.Stage & (U32 & List<&2, C.Vec3>)):
  do IO<C.Stage & (U32 & List<&2, C.Vec3>)>:
    +a : C.Asset <- C.Asset.load(Fire.mesh(), False{})
    man : C.Asset <- C.Asset.load("assets/imported/metal-man/metal-man.mesh", True{})
    Fire.built(Fire.cast(C.Cast.add(C.Cast.add(C.Cast.none(), a, C.none(), C.Mat4.id(), Nil{}, fps), man, C.none(), C.Mat4.mul(C.Mat4.move((0.0 - 0.2 : F32), (0.0 - 0.29 : F32), 0.0), C.Mat4.mul(C.Mat4.turn_y((0.0 - 1.5708 : F32)), C.Mat4.scale(0.06))), C.Play{0} <> C.Slide{(0.0 - 0.0035 : F32), 0.0, 0.0} <> Nil{}, fps)), fps, Fire.spots(Fire.fit(a)))

def Fire.go(r: C.Stage & (U32 & List<&2, C.Vec3>), +fps: U32, +cam: C.Cam, +render: C.Render, +ns: Nat, +frames: U32, +prefix: String) -> IO(Unit):
  (s, bs) = r
  (base, spots) = bs
  Fire.run(s, base, fps, cam, render, ns, frames, prefix, spots)

def main() -> IO(Unit):
  do IO<Unit>:
    r : C.Stage & (U32 & List<&2, C.Vec3>) <- Fire.setup(24)
    Fire.go(r, 24, C.Cam.court(), C.Render{16, 0}, 128n, 120, "out/frame")
