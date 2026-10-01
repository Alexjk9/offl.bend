import Base
import ./core.bend as C
import ./scene.bend as F

type Ed is Data:
  Ed{t0: Nat, mark: Nat, +marked: U32, +steps: U32, +frame: U32, +mode: U32, +paused: Bool, +ex: F32, +ey: F32, +ez: F32, +yaw: F32, +pitch: F32, +moved: Bool, +quit: Bool, +vf: F32, +vs: F32, +vu: F32, last: Nat}

def Ed.of(+t0: Nat, cam: C.Cam) -> Ed:
  C.Cam{_, _, _, _, _, _, fx, fy, fz, ex, ey, ez} = cam
  Ed{t0, t0, 0, 0, 0, 0, False{}, ex, ey, ez, F32.atan2((0.0 - fx : F32), fz), F32.asin(F32.clamp(fy, (0.0 - 1.0 : F32), 1.0)), False{}, False{}, 0.0, 0.0, 0.0, t0}

def Ed.cam(ed: Ed) -> C.Cam:
  Ed{_, _, _, _, _, _, _, ex, ey, ez, yaw, pitch, _, _, _, _, _, _} = ed
  C.Cam.look(ex, ey, ez, yaw, pitch)

def Ed.paused(ed: Ed) -> Bool:
  Ed{_, _, _, _, _, _, paused, _, _, _, _, _, _, _, _, _, _, _} = ed
  paused

def Ed.moved(ed: Ed) -> Bool:
  Ed{_, _, _, _, _, _, _, _, _, _, _, _, moved, _, _, _, _, _} = ed
  moved

def Ed.frame(ed: Ed) -> U32:
  Ed{_, _, _, _, frame, _, _, _, _, _, _, _, _, _, _, _, _, _} = ed
  frame

def Ed.mode(ed: Ed) -> U32:
  Ed{_, _, _, _, _, mode, _, _, _, _, _, _, _, _, _, _, _, _} = ed
  mode

def Ed.steps(ed: Ed) -> U32:
  Ed{_, _, _, steps, _, _, _, _, _, _, _, _, _, _, _, _, _, _} = ed
  steps

def Ed.done(ed: Ed) -> Bool:
  Ed{_, _, _, _, _, _, _, _, _, _, _, _, _, quit, _, _, _, _} = ed
  quit

def Ed.last(ed: Ed) -> Nat:
  Ed{_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, last} = ed
  last

def Ed.still(ed: Ed) -> Bool:
  Ed{_, _, _, _, _, _, _, _, _, _, _, _, _, _, vf, vs, vu, _} = ed
  F32.is_eq(vf, 0.0) && F32.is_eq(vs, 0.0) && F32.is_eq(vu, 0.0)

def Ed.walk(ed: Ed, +fwd: F32, +side: F32, +up: F32) -> Ed:
  Ed{t0, mark, marked, steps, frame, mode, paused, ex, ey, ez, +yaw, +pitch, _, quit, vf, vs, vu, last} = ed
  +yc = F32.cos(yaw)
  +ys = F32.sin(yaw)
  +pc = F32.cos(pitch)
  +ps = F32.sin(pitch)
  Ed{t0, mark, marked, steps, frame, mode, paused, (ex - fwd * ys * pc + side * yc : F32), (ey + fwd * ps + up : F32), (ez + fwd * yc * pc + side * ys : F32), yaw, pitch, True{}, quit, vf, vs, vu, last}

def Ed.turn(ed: Ed, +dyaw: F32, +dpitch: F32) -> Ed:
  Ed{t0, mark, marked, steps, frame, mode, paused, ex, ey, ez, yaw, pitch, _, quit, vf, vs, vu, last} = ed
  Ed{t0, mark, marked, steps, frame, mode, paused, ex, ey, ez, (yaw + dyaw : F32), F32.clamp((pitch + dpitch : F32), (0.0 - 1.5 : F32), 1.5), True{}, quit, vf, vs, vu, last}

def Ed.move(ed: Ed, +f: F32, +s: F32, +u: F32) -> Ed:
  Ed{t0, mark, marked, steps, frame, mode, paused, ex, ey, ez, yaw, pitch, moved, quit, _, _, _, last} = ed
  Ed{t0, mark, marked, steps, frame, mode, paused, ex, ey, ez, yaw, pitch, moved, quit, f, s, u, last}

def Ed.set(ed: Ed, +m: U32) -> Ed:
  Ed{t0, mark, marked, steps, frame, _, paused, ex, ey, ez, yaw, pitch, _, quit, vf, vs, vu, last} = ed
  Ed{t0, mark, marked, steps, frame, m, paused, ex, ey, ez, yaw, pitch, True{}, quit, vf, vs, vu, last}

def Ed.pause(ed: Ed) -> Ed:
  Ed{t0, mark, marked, steps, frame, mode, paused, ex, ey, ez, yaw, pitch, moved, quit, vf, vs, vu, last} = ed
  Ed{t0, mark, marked, steps, frame, mode, Bool.not(paused), ex, ey, ez, yaw, pitch, moved, quit, vf, vs, vu, last}

def Ed.stop(ed: Ed) -> Ed:
  Ed{t0, mark, marked, steps, frame, mode, paused, ex, ey, ez, yaw, pitch, moved, _, vf, vs, vu, last} = ed
  Ed{t0, mark, marked, steps, frame, mode, paused, ex, ey, ez, yaw, pitch, moved, True{}, vf, vs, vu, last}

def Ed.stamp(ed: Ed, now: Nat) -> Ed:
  Ed{t0, mark, marked, steps, frame, mode, paused, ex, ey, ez, yaw, pitch, moved, quit, vf, vs, vu, _} = ed
  Ed{t0, mark, marked, steps, frame, mode, paused, ex, ey, ez, yaw, pitch, moved, quit, vf, vs, vu, now}

def Ed.speed() -> F32:
  1.0

def Ed.slide2(still: Bool, +ed: Ed, +dt: F32) -> Ed:
  match still:
    case True{}:
      ed
    case False{}:
      Ed{_, _, _, _, _, _, _, _, _, _, _, _, _, _, vf, vs, vu, _} = ed
      Ed.walk(ed, (vf * dt : F32), (vs * dt : F32), (vu * dt : F32))

def Ed.slide(+ed: Ed, +now: Nat) -> Ed:
  +dt = (F32.from_nat(Nat.sub(now, Ed.last(ed))) * Ed.speed() / 1000.0 : F32)
  Ed.stamp(Ed.slide2(Ed.still(ed), ed, dt), now)

def Ed.tick(ed: Ed, +ns: Nat) -> Ed:
  Ed{t0, mark, marked, steps, +frame, mode, +paused, ex, ey, ez, yaw, pitch, _, quit, vf, vs, vu, last} = ed
  Ed{t0, mark, marked, (steps + U32.from_nat(ns) : U32), C.sel(~U32, paused, frame, (frame + 1 : U32)), mode, paused, ex, ey, ez, yaw, pitch, False{}, quit, vf, vs, vu, last}

def Ed.event(e: Event, ed: Ed) -> Ed:
  match e:
    case Close{}:
      Ed.stop(ed)
    case _:
      ed

def Ed.events(es: List<Event>, ed: Ed) -> Ed:
  match es:
    case []:
      ed
    case e <> rest:
      Ed.events(rest, Ed.event(e, ed))

def Ed.name(+mode: U32) -> String:
  match mode:
    case 0:
      "lit"
    case 1:
      "solid"
    case _:
      "textured"

def Ed.state(paused: Bool) -> String:
  match paused:
    case True{}:
      "  paused"
    case False{}:
      ""

def Ed.reset(pb: C.Live()) -> C.Live():
  (st, w) = pb
  (C.Reset.show(st), w)

def Ed.drop(pc: C.Live() & C.Cam) -> IO(C.Live()):
  (pb, _) = pc
  IO.pure(C.Live(), pb)

def Ed.advance(paused: Bool, moved: Bool, +tick: F.Fire, +frame: U32, pb: C.Live()) -> IO(C.Live()):
  match paused moved:
    case False{} _:
      do IO<C.Live()>:
        pc : C.Live() & C.Cam <- F.Fire.world(tick, frame, pb)
        Ed.drop(pc)
    case True{} True{}:
      IO.pure(C.Live(), Ed.reset(pb))
    case True{} False{}:
      IO.pure(C.Live(), pb)

def Ed.cmd4(m: Maybe<&2, U32>, ed: Ed) -> Ed:
  match m:
    case None{}:
      ed
    case Some{v}:
      Ed.set(ed, v)

def Ed.cmd3(ok: Bool, arg: String, ed: Ed) -> Ed:
  match ok:
    case True{}:
      Ed.cmd4(U32.read(String.trim(arg)), ed)
    case False{}:
      ed

def Ed.cmd.pause(ok: Bool, ed: Ed) -> Ed:
  match ok:
    case True{}:
      Ed.pause(ed)
    case False{}:
      ed

def Ed.cmd.turn(ok: Bool, a: String, b: String, ed: Ed) -> Ed:
  match ok:
    case True{}:
      Ed.turn(ed, C.Env.f32(a), C.Env.f32(b))
    case False{}:
      ed

def Ed.cmd.walk(ok: Bool, a: String, b: String, c: String, ed: Ed) -> Ed:
  match ok:
    case True{}:
      Ed.walk(ed, C.Env.f32(a), C.Env.f32(b), C.Env.f32(c))
    case False{}:
      ed

def Ed.cmd2(parts: List<&2, String>, ed: Ed) -> Ed:
  match parts:
    case verb <> Nil{}:
      Ed.cmd.pause(String.eq(verb, "pause"), ed)
    case verb <> a <> Nil{}:
      Ed.cmd3(String.eq(verb, "mode"), a, ed)
    case verb <> a <> b <> Nil{}:
      Ed.cmd.turn(String.eq(verb, "turn"), a, b, ed)
    case verb <> a <> b <> c <> _:
      Ed.cmd.walk(String.eq(verb, "walk"), a, b, c, ed)
    case _:
      ed

def Ed.cmd(line: String, ed: Ed) -> Ed:
  Ed.cmd2(String.split(String.trim(line), ' '), ed)

def Ed.cmds(lines: List<&2, String>, ed: Ed) -> Ed:
  match lines:
    case Nil{}:
      ed
    case l <> rest:
      Ed.cmds(rest, Ed.cmd(l, ed))

def Ed.text(r: Result<&1, &1, U32 & String, Maybe<&1, String>>) -> String:
  match r:
    case Done{Some{text}}:
      text
    case _:
      ""

def Ed.log(empty: Bool, text: String) -> IO(Unit):
  match empty:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.print("ui: " ++ String.trim(text))

def Ed.title(due: Bool, window: Window, sock: Socket, +now: Nat, ed: Ed, last: Image & C.Live(), rest: Window -> Socket -> Ed -> (Image & C.Live()) -> IO(Unit)) -> IO(Unit):
  match due:
    case False{}:
      rest(window, sock, ed, last)
    case True{}:
      Ed{t0, mark, +marked, +steps, frame, +mode, +paused, ex, ey, ez, yaw, pitch, moved, quit, vf, vs, vu, at} = ed
      do IO<Unit>:
        w2 : Window <- Window.set_title(window, "Editor  " ++ Ed.name(mode) ++ "  " ++ U32.show(steps) ++ " steps  " ++ F32.show((U32.to_f32(U32.from_nat(Nat.sub(now, mark))) / U32.to_f32(C.sel(~U32, U32.is_eq(steps, marked), 1, (steps - marked : U32))) : F32)) ++ " ms/step" ++ Ed.state(paused))
        rest(w2, sock, Ed{t0, now, steps, steps, frame, mode, paused, ex, ey, ez, yaw, pitch, moved, quit, vf, vs, vu, at}, last)

def Ed.mark(ed: Ed) -> Nat:
  Ed{_, mark, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _} = ed
  mark

def Ed.go(quit: Bool, window: Window, sock: Socket, +ed: Ed, last: Image & C.Live(), rest: Window -> Socket -> Ed -> (Image & C.Live()) -> IO(Unit)) -> IO(Unit):
  match quit:
    case True{}:
      do IO<Unit>:
        Unit <- Window.close(window)
        Socket.close(sock)
    case False{}:
      do IO<Unit>:
        +now : Nat <- IO.now()
        Ed.title(Nat.is_le(1000n, Nat.sub(now, Ed.mark(ed))), window, sock, now, ed, last, rest)

def Ed.next(window: Window, sock: Socket, +ed: Ed, last: Image & C.Live(), rest: Window -> Socket -> Ed -> (Image & C.Live()) -> IO(Unit)) -> IO(Unit):
  Ed.go(Ed.done(ed), window, sock, ed, last, rest)

def Ed.after(shown: Window & Image & List<Event>, sock: Socket, pb: C.Live(), ed: Ed, rest: Window -> Socket -> Ed -> (Image & C.Live()) -> IO(Unit)) -> IO(Unit):
  (window, image, events) = shown
  Ed.next(window, sock, Ed.events(events, ed), (image, pb), rest)

def Ed.shown(window: Window, sock: Socket, drawn: Image & C.Live(), ed: Ed, rest: Window -> Socket -> Ed -> (Image & C.Live()) -> IO(Unit)) -> IO(Unit):
  (image, pb) = drawn
  do IO<Unit>:
    shown : Window & Image & List<Event> <- Window.frame(window, image)
    Ed.after(shown, sock, pb, ed, rest)

def Ed.act(window: Window, sock: Socket, +ed: Ed, +tick: F.Fire, +yp: F32, +pt: C.Portal, +bounces: U32, +ns: Nat, last: Image & C.Live(), rest: Window -> Socket -> Ed -> (Image & C.Live()) -> IO(Unit)) -> IO(Unit):
  (old, pb) = last
  do IO<Unit>:
    pb2 : C.Live() <- Ed.advance(Ed.paused(ed), Ed.moved(ed), tick, Ed.frame(ed), pb)
    p2 : C.Live() <- IO.pure(C.Live(), C.Run.steps(ns, pb2, yp, pt, Ed.cam(ed), C.Render{bounces, Ed.mode(ed)}, Ed.steps(ed)))
    drawn : Image & C.Live() <- IO.pure(Image & C.Live(), C.Run.view(p2, old))
    Ed.shown(window, sock, drawn, Ed.tick(ed, ns), rest)

def Ed.run(window: Window, sock: Socket, ed: Ed, +tick: F.Fire, +yp: F32, +pt: C.Portal, +bounces: U32, +ns: Nat, last: Image & C.Live(), rest: Window -> Socket -> Ed -> (Image & C.Live()) -> IO(Unit)) -> IO(Unit):
  Ed.act(window, sock, ed, tick, yp, pt, bounces, ns, last, rest)

def Ed.polled(window: Window, p: Socket & Result<&1, &1, U32 & String, Maybe<&1, String>>, ed: Ed, +tick: F.Fire, +yp: F32, +pt: C.Portal, +bounces: U32, +ns: Nat, last: Image & C.Live(), rest: Window -> Socket -> Ed -> (Image & C.Live()) -> IO(Unit)) -> IO(Unit):
  (sock, r) = p
  +text = Ed.text(r)
  do IO<Unit>:
    Unit <- Ed.log(String.is_empty(text), text)
    Ed.run(window, sock, Ed.cmds(String.lines(text), ed), tick, yp, pt, bounces, ns, last, rest)

def Ed.step(window: Window, sock: Socket, ed: Ed, +tick: F.Fire, +yp: F32, +pt: C.Portal, +bounces: U32, +ns: Nat, last: Image & C.Live(), rest: Window -> Socket -> Ed -> (Image & C.Live()) -> IO(Unit)) -> IO(Unit):
  do IO<Unit>:
    p : Socket & Result<&1, &1, U32 & String, Maybe<&1, String>> <- TCP.poll(sock, 4096, 0)
    Ed.polled(window, p, ed, tick, yp, pt, bounces, ns, last, rest)

def Ed.loop(fuel: Nat, window: Window, sock: Socket, ed: Ed, +tick: F.Fire, +yp: F32, +pt: C.Portal, +bounces: U32, +ns: Nat, last: Image & C.Live()) -> IO(Unit):
  match fuel:
    case 0n:
      do IO<Unit>:
        Unit <- Window.close(window)
        Socket.close(sock)
    case 1n+f:
      Ed.step(window, sock, ed, tick, yp, pt, bounces, ns, last, w => s => e => l => Ed.loop(f, w, s, e, tick, yp, pt, bounces, ns, l))

def Ed.accepted(a: Listener & C.Got(Socket)) -> IO(Socket):
  (l, r) = a
  do IO<Socket>:
    Unit <- Listener.close(l)
    IO.pass(Socket, r)

def Ed.serve(+port: U32) -> IO(Socket):
  do IO<Socket>:
    Unit <- IO.print("editor: waiting for the UI on port " ++ U32.show(port))
    l : Listener <- IO.try(Listener, TCP.listen("127.0.0.1", port))
    a : Listener & C.Got(Socket) <- TCP.accept(l)
    Ed.accepted(a)

def Ed.start(s: C.Stage, +base: U32, spots: List<&2, C.Vec3>, +fps: U32, +cam: C.Cam, +bounces: U32, +ns: Nat, +port: U32) -> IO(Unit):
  C.Stage{bvh, lights, +insts, mats, ems, +eyes, +cuts, +yp, +pt, _} = s
  do IO<Unit>:
    sock : Socket <- Ed.serve(port)
    window : Window <- IO.try(Window, Window.open("Editor", 2048, 1024))
    st : C.PT = C.Init.show()
    +t0 : Nat <- IO.now()
    Ed.loop(4294967295n, window, sock, Ed.of(t0, C.Stage.cam(C.Stage.worlds(insts, 0, fps), eyes, cuts, 0, cam)), F.Fire{insts, ems, fps, eyes, cuts, cam, yp, pt, C.Render{bounces, 0}, ns, base, "", spots}, yp, pt, bounces, ns, (Pix{0}, (st, (bvh, (mats, lights)))))

def Probe.loop(left: Nat, p: C.Live(), +yp: F32, +pt: C.Portal, +cam: C.Cam, +render: C.Render, +fs: U32, +us: U32) -> IO(U32 & C.Live()):
  match left:
    case 0n:
      IO.pure(U32 & C.Live(), (us, p))
    case 1n+k:
      do IO<U32 & C.Live()>:
        a : Nat <- IO.now()
        p2 : C.Live() <- IO.pure(C.Live(), C.Run.one(p, yp, pt, cam, render, fs))
        b : Nat <- IO.now()
        Probe.loop(k, p2, yp, pt, cam, render, (fs + 1 : U32), (us + 1000 * U32.from_nat(Nat.sub(b, a)) : U32))

def Probe.write(r: String & Image, path: C.Got(String)) -> IO(Unit):
  (text, img) = r
  C.Dump.write(path, text)

def Probe.dump(drawn: Image & C.Live(), path: C.Got(String)) -> IO(Unit):
  (img, pb) = drawn
  Probe.write(C.Dump.take(img), path)

def Probe.report(r: U32 & C.Live(), +n: U32, path: C.Got(String)) -> IO(Unit):
  (us, p) = r
  do IO<Unit>:
    Unit <- IO.print("steps " ++ U32.show(n) ++ " trace " ++ U32.show((us / C.sel(~U32, U32.is_eq(n, 0), 1, n) : U32)) ++ " us")
    a : Nat <- IO.now()
    drawn : Image & C.Live() <- IO.pure(Image & C.Live(), C.Run.view(p, Pix{0}))
    b : Nat <- IO.now()
    Unit <- IO.print("view " ++ Nat.show(Nat.sub(b, a)) ++ " ms")
    Probe.dump(drawn, path)

def Probe.run(+n: Nat, s: C.Stage, +cam: C.Cam, +render: C.Render, path: C.Got(String)) -> IO(Unit):
  C.Stage{bvh, lights, _, mats, _, _, _, yp, pt, _} = s
  do IO<Unit>:
    st : C.PT = C.Init.show()
    r : U32 & C.Live() <- Probe.loop(n, (st, (bvh, (mats, lights))), yp, pt, cam, render, 0, 0)
    Probe.report(r, U32.from_nat(n), path)

def Main.mode(probe: C.Got(String), ppm: C.Got(String), r: C.Stage & (U32 & List<&2, C.Vec3>), +fps: U32, +cam: C.Cam, +bounces: U32, +ns: Nat, +port: U32) -> IO(Unit):
  match probe:
    case Fail{_}:
      (s, bs) = r
      (base, spots) = bs
      Ed.start(s, base, spots, fps, cam, bounces, ns, port)
    case Done{text}:
      (s, _) = r
      Probe.run(U32.to_nat(C.Env.read(Done{text}, 40)), s, cam, C.Render{bounces, 0}, ppm)

def main() -> IO(Unit):
  do IO<Unit>:
    bounces : U32 <- C.Env.num("PT_BOUNCES", 16)
    steps : U32 <- C.Env.num("PT_STEPS", 2)
    +fps : U32 <- C.Env.num("PT_FPS", 24)
    port : U32 <- C.Env.num("PT_PORT", 7777)
    cam : C.Got(String) <- IO.get_env("PT_CAM")
    probe : C.Got(String) <- IO.get_env("PT_PROBE")
    ppm : C.Got(String) <- IO.get_env("PT_PPM")
    r : C.Stage & (U32 & List<&2, C.Vec3>) <- F.Fire.setup(fps)
    Main.mode(probe, ppm, r, fps, C.Env.cam(cam), bounces, U32.to_nat(steps), port)
