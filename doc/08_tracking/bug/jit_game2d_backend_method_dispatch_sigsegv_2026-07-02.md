# Bug: JIT SIGSEGV calling GameBackend trait methods via `LoopDriver.step`

**Date:** 2026-07-02
**Component:** Cranelift JIT path (`bin/simple run` / `src/compiler_rust/target/release/simple run`),
`src/lib/nogc_sync_mut/game2d/{backend,loop}/*.spl`.

## Symptom

Any game2d app that drives frames through `LoopDriver.step(app, backend, snapshot, dt_ns)`
(the same call `run_frames` and `game2d.app.run.run_config` use) SIGSEGVs when run via
`bin/simple run <file>.spl`, even for a single frame and a trivial `App`/`GameBackend` pair:

```simple
use std.nogc_sync_mut.game2d.backend.headless.{HeadlessBackend}
use std.nogc_sync_mut.game2d.loop.driver.{LoopDriver}
use std.nogc_sync_mut.game2d.input.snapshot.{InputSnapshot}
use std.nogc_sync_mut.game2d.render.canvas.{Canvas}

class TinyApp:
    x: i64
    fn load(self): pass_do_nothing
    fn update(self, dt: f32): val _ = dt
    me fixed_update(self, step: f32): val _ = step
    fn draw(self, ctx: Canvas): val _ = ctx

fn main():
    var backend = HeadlessBackend.create(64, 48)
    var app = TinyApp(x: 0)
    var driver = LoopDriver.new(60)
    var snap = InputSnapshot.create()
    driver.step(app, backend, snap, 16_666_667)   # <-- SIGSEGV, JIT thread jumps to 0x0
```

`gdb` shows the crashing thread ("simple-main") jumping into unmapped/garbage
JIT-generated code (`0x0000020a3cfd3625 in ?? ()`, no symbols) — this is a
Cranelift codegen/linking defect, not a Simple-level logic error.

`bin/simple test <spec-with-the-same-call>.spl` does **not** crash — the
interpreter path is unaffected (`test/03_system/game2d/game2d_event_replay_spec.spl`
exercises the identical `run_frames` → `driver.step` path and passes green).

## Root-cause investigation (bisected)

- Not the array-of-struct parameter on `poll_events(self, events_out: [Event])`:
  a plain function `fn f(xs: [Event]) -> i64` works fine; a method
  `Mini.poll_events(self, events_out: [Event])` on an unrelated class crashes
  **only once `Event` is imported from `game2d.backend.trait`**, and crashes
  even with the array parameter removed entirely
  (`fn poll_events(self) -> i64: 0` still SIGSEGVs).
- Renaming the method fixes the *isolated* repro: `Mini.poll_native_events_xyz()`
  works. This proves the JIT resolves at least some method calls by **bare
  name across co-compiled definitions**, matching the compiler's own existing
  guard for private helpers: `warning: private helper '_pack_rgba' has 2
  co-compiled definitions with 2 differing signatures ... calls resolve by
  bare name (last-write-wins) and may dispatch to the wrong one — silent
  wrong-result or SIGSEGV` (seen verbatim running
  `examples/11_advanced/game2d/breakout/main.spl`, which co-compiles
  `engine/render/pipeline.spl::_pack_rgba(r,g,b,a)` against
  `game2d/backend/headless.spl::_pack_rgba(c: EngineColor)`). That guard only
  fires for `_`-prefixed private helpers; it does not catch (or fix) public
  trait methods.
- **However**, renaming all 8 `GameBackend` trait methods to unique
  `gb_*`/`poll_native_events` names (done in `trait.spl`, `headless.spl`,
  `sdl_backend.spl`, with call sites updated in `loop/driver.spl`) does
  **not** fix the full `driver.step` repro above — it still SIGSEGVs at the
  `gb_begin_frame()` call. So the collision is not fully explained by
  same-named `GameBackend` trait methods alone; some other co-compiled
  symbol (candidates: the `_pack_rgba` collision above, or one of the many
  unrelated classes across the tree that also define `begin_frame`/
  `end_frame`/`shutdown` as *inherent* methods — grep finds 30–100+ such
  definitions with differing signatures, e.g. `engine3d/backend_*.spl`,
  `compositor/frame.spl`, `gpu/*_session.spl`) still corrupts the
  co-compiled unit. The "co-compiled" set is clearly broader than the
  transitive `use` graph — `game2d/backend/headless.spl` does not import
  `engine/render/pipeline.spl` (where the colliding `_pack_rgba` lives) yet
  the collision warning fires anyway when both get pulled into the same run.

## Impact

- `game2d.app.run.run()` / `run_config()` — the documented top-level game
  entry point — cannot be exercised via `bin/simple run` today; it will
  SIGSEGV on the very first frame for any app.
- Any custom game loop built directly on `LoopDriver.step` (this is what
  `src/app/game.breakout/` does) hits the same wall.

## Workaround (in use by `src/app/game.breakout/`)

Drive all game2d session/capture/perf logic through **`bin/simple test`**
(SPipe spec runner, interpreter path) instead of `bin/simple run`. Confirmed
non-crashing for the full `driver.step` call chain. Trade-off: interpreter
throughput is far below JIT (~0.4 ms/frame for a no-op app at 64×48). The
headless rectangle path now clips once and writes framebuffer rows directly,
which improved the Breakout rendered smoke to `lowres_frame_time_ms=12`; the
target 800×600 frame-time budget still requires the JIT/native `LoopDriver.step`
path to stop crashing. `test/03_system/game2d/breakout_production_spec.spl`
documents the actual measured frame-time numbers under this constraint rather
than silently asserting a JIT-only budget.

## Suggested fix (not attempted — Rust seed, out of scope for this lane)

The JIT's method-symbol table needs to key dispatch by `(owning type, method
name)`, not bare method name, for both trait-declared and inherent methods.
Short of that, the existing `_pack_rgba`-style collision detector should be
extended to (a) cover non-`_`-prefixed / public methods, and (b) hard-fail
(refuse to JIT, fall back to interpreter) instead of silently emitting a
possibly-wrong compiled unit that can SIGSEGV.
