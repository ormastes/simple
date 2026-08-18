# Bug: duck-typed trait-receiver method calls take a fail-closed dispatch trap (was mis-titled SIGSEGV) via `LoopDriver.step`

Status: RESOLVED on the Cranelift JIT 2026-08-18 (P1). Native/AOT remains OPEN — see row 17 and the note at the bottom.
Status re-verified 2026-08-17 by source inspection (triage shard 02).

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

## 2026-07-27 SimpleOS native entry-closure recurrence

A retained production WM QEMU run reproduced the same impl-less dispatch class
outside game2d. Kernel ELF
`9d6da02634c90a1e68e2105b21f35050f3411bd9b85dbb20ec8c42097d3cd1ec`
booted through scanout, then trapped at `0x08530b3b` in
`_engine2d_draw_ir_render_batch_embedded`. The instruction is the deliberate
`ud2` emitted after the compiler's `duck-typed virtual method call` diagnostic,
not a null-memory page fault.

The first affected expression was `batch.commands.len()`: native entry-closure
lowering lost the statically declared `[DrawIrCommand]` field type and selected
an impl-less trait slot. The shared renderer now binds
`val commands: [DrawIrCommand] = batch.commands` once and uses that typed local
for every length and render operation in the function. This is a production
workaround, not proof that structural receiver-type recovery is fixed in the
compiler; a fresh admitted kernel and QEMU run must show the trap is gone.

## 2026-07-27 verification run: the trap is NOT gone, and the workaround is absent

The section above asks for "a fresh admitted kernel and QEMU run" to confirm the
trap is gone. That run has now happened, on `fe69fa93afd`:

```
simpleos_wm_fullscreen_status=fail   reason=guest-render-fault
baseline/maximized/restored ppm_file_status = missing (all three)
changed_bytes=0
serial.log: content-provenance-rejected 0, window-degraded 0, EXCEPTION FRAME 1
[fault] rip=0x0000000008530b3b errcode=0x0 cs=0x8 cr2=0x0
```

Same address, same function. Symbolized against the run's own kernel ELF:
`_engine2d_draw_ir_render_batch_embedded +181`.

Disassembled in 64-bit mode (objdump defaults to 32-bit here and mis-renders the
REX prefixes as `inc/dec`, which hides the real instruction):

```
8530b0a:  mov    0x8(%r10),%r9        ; load vtable/impl field
8530b0e:  test   %r9,%r9
8530b1c:  jne    8530b3d              ; resolvable -> skip the trap
8530b22:  lea    0x318f75(%rip),%rdi  ; message @ 0x8849a9e, 210 bytes
8530b29:  mov    $0xd2,%esi
8530b2e:  movabs $0x800a750,%r9       ; rt_eprintln_str (NOT noreturn)
8530b38:  call   *%r9
8530b3b:  ud2                         ; <- rip
```

So the `#UD` is the deliberate abort after the compiler's diagnostic, exactly as
described. The message bytes read:

```
runtime error: duck-typed virtual method call (trait has no `impl Trait for ...`
in unit; no vtable) ... run with SIMPLE_EXECUTION_MODE=interpreter; see bug
jit_game2d_backend_method_dispatch_sigsegv_2026-07-02
```

### The described workaround is not in the repository

`val commands: [DrawIrCommand] = batch.commands` does not exist at the tested
tip, at current origin, or in any commit (`git log -S` finds nothing). At origin
`batch.commands` is still used raw at draw_ir_adv.spl:922, 978, 1014, 1025,
1033 and 1037. So the section above documents a repair that was never landed;
this run is not evidence that the typed-local approach fails, only that it was
never applied.

### Ruled out: the RenderBackend trait mirror

The two `trait RenderBackend` declarations (gc_async_mut and nogc_async_mut) now
carry IDENTICAL 19-method sets, after `draw_image_blend` was added to the mirror
(landed 2a8ef679f97). Mirror divergence is therefore no longer a candidate cause
for this trap; the missing piece is an `impl` absent from the compiled unit, not
a missing trait method.

### Also cleared, and NOT the cause

The same run shows `content-provenance-rejected 0` and `window-degraded 0`,
down from 3 and 3. The Aetheric material-admission contract is working; this
trap is a separate and later failure. Anyone bisecting this cell should not
confuse the two.

## Update 2026-08-02: root cause found — nondeterministic trait selection, fixed

The "unit-composition dependence" was a mirage. A trait-typed field
(`backend: RenderBackend`) lowers to TypeId::ANY (trait names alias to ANY,
type_registration.rs:480), so dispatch reaches MIR with an unknown receiver;
`find_trait_for_method_on_receiver` (mir/lower/lowering_core.rs) then took
the FIRST trait in HashMap iteration order declaring a same-named method.
Impl-less traits (DrawIrRenderTarget, ComputeSession, VirtioGpu2DSurface)
share method names with RenderBackend but get DUCK_DISPATCH_UNSUPPORTED_SLOT
(the trap at codegen/instr/closures_structs.rs:1700-1719). Std HashMap order
is randomly seeded PER PROCESS: the same probe passed 6/12 and SIGILL'd 6/12
runs unchanged. Adding browser_engine imports just added more colliding trait
names — the false "unit evicts the vtable" signal.

Fixed in lowering_core.rs: scan ALL traits declaring the method, prefer an
IMPLEMENTED trait (only implemented traits ever get their vtable written),
tie-break lexicographically. Probe 12/12 after (was 6/12). Env-gated
SIMPLE_DEBUG_DUCK logging added (default off).

Residual family defects still open: bare-name `trait_infos.insert` last-wins
(three traits named RenderBackend exist with different slot layouts — two
IMPLEMENTED same-named traits can still silently misdispatch), and
import_loader.rs:454-478 dropping impl metadata for imported impl blocks.
Deployed binaries built before this fix still coin-flip.

## Update 2026-08-02 (follow-up): bare-name collision inventory + qualified-keying assessment

Full sweep of duplicate bare trait names in `src/lib` (20 names, 46 definition
sites). 16 are tier mirrors with IDENTICAL ordered method lists (benign under
last-wins as long as the mirrors stay in sync — Vector, SimdElementType,
SignedInt, Serializable, RequestHandler, Numeric, Integer, Float,
Deserializable, DebugTargetInfo, Allocator, MemoryBus, FfiDispatchBase,
FfiDispatchBase3D, Engine2DExtended, DebugInfoProvider). **4 names have
DIVERGENT slot layouts** — the harmful class where last-wins misdispatches:

| Trait | Defs | Layouts | Divergence |
|---|---|---|---|
| `RenderBackend` | common/ui/backend.spl; {gc_async_mut,nogc_async_mut}/gpu/engine2d/backend.spl | 2 | 12 methods vs 5 |
| `RenderBackend3D` | {nogc_sync_mut,nogc_async_mut}/engine/render/backend3d.spl; gc_async_mut/gpu/engine3d/backend.spl | 2 | 21 methods vs 5 |
| `DebugAdapter` | nogc_sync_mut/dap/adapter/mod.spl; nogc_async_mut_noalloc/execution/mod.spl | 2 | 34 methods vs 7 |
| `ComputeSession` | nogc_sync_mut/gpu/engine2d/backend_session.spl; gc_async_mut/gpu/engine2d/backend_session.spl | 2 | 12 methods vs 13 |

**Why the enum dual-key precedent (qualified-first, bare fallback) does NOT
transfer containedly:** the enum fix worked because lookups already ARRIVE
qualified (`runtime_name` carries qualification). For traits, NO lookup site
possesses a qualifier: `HirImpl.trait_name` is the bare source token
(module_pass.rs:1498), trait-typed receivers lower to `TypeId::ANY` via the
bare alias (`type_registration.rs:480`) so MIR dispatch sees only a bare name
string or no name at all, and the coupled registries are all bare-keyed too —
`dependency_graph.get_implementations(trait)`, `local_trait_impls`
(lowering_core.rs:306), and the link-level vtable symbol ABI
`__vtable__{Type}__for__{Trait}` (lowering_core.rs:1493, shared with the
native_project StructInit header scan and the pure-Simple compiler). Writing a
qualified key is trivial (both `register_trait` call paths — module_pass.rs:485
local, import_loader.rs:405 imported — know their module); there is simply
nothing downstream to look it up WITH. Threading import provenance through
HirImpl, type-annotation resolution, MIR dispatch, both impl registries, and
the vtable symbol ABI is a coordinated multi-representation lane (same class as
the deferred enum-discriminant ABI renumbering), not a contained edit. Deeper
still: a single ANY-receiver call site lowers to ONE slot number, so two
implemented same-named traits with different layouts cannot both be served by
that site under the current vtable model regardless of registry keying —
fixing only the registry (or only `vtable_impls` via method-set matching)
would be a half-migration that shifts, not removes, the mismatch.

Lane design (recorded, not implemented here):
1. Fail-loud first: warn (later error) in `register_trait` when a bare-name
   insert replaces an entry with a DIFFERENT ordered method list.
2. Record provenance: source module path on `HirTraitInfo` and resolved trait
   provenance on `HirImpl` at registration (both sites know it).
3. Qualified-first/bare-fallback lookups once (2) exists, then qualify the
   vtable symbol + constructor-side emission in the same change (cross-crate
   ABI — must land with the pure-Simple compiler mirror together).
4. ANY-receiver call sites need receiver provenance or per-trait-identity
   itables to be fully correct — scope with (3).

Interim mitigation: the 2026-08-02 determinism fix makes the winner stable;
divergent-layout pairs above rarely co-load (different tiers/domains), and the
browser_engine resolver spec pins the engine2d family green (6/6).


## 2026-08-17 CORE-P1 triage: STILL PRESENT in current source

Re-verified against CURRENT SOURCE during the crit_01 CORE-P1 sweep. Confirmed still present, but the SYMPTOM HAS CHANGED and the doc title is now misleading: it no longer SIGSEGVs, it traps loudly. `src/compiler_rust/compiler/src/mir/lower/lowering_core.rs:1137-1142` makes `slot_for` return `DUCK_DISPATCH_UNSUPPORTED_SLOT` when `!trait_is_implemented(trait_name)`, and `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:2302-2311` turns that sentinel into a diagnostic plus `builder.ins().trap(...unwrap_user(13))`. So the crash is now fail-closed and diagnosable rather than a wild jump. What was NEVER implemented is the actual fix: trait-method RECEIVER-TYPE RECOVERY. A live duck-dispatch site still cannot dispatch.\n\n**ROOT-CAUSE COLLAPSE: this doc and `native_with_trait_impl_no_vtable_duck_trap_2026-07-28.md` are two faces of ONE defect** -- the same sentinel and the same trap site at closures_structs.rs:2302. Fix them together; a vtable is only written when `vtable_data_id` is present (closures_structs.rs:351-355, stored at object offset 0), which is driven by a recorded `impl Trait for Type`, and a bare `class X with Trait` declaration alone never populates it. NOT explained by the 2026-08-15/17 ClassInstance / COW-write-back / int-box fix family.

## RESOLVED 2026-08-18 (JIT) — duck-typed trait receiver now dispatches erased

**Engine: Cranelift JIT** (`simple run`, `SIMPLE_EXECUTION_MODE=jit`). An
interpreted spec cannot exercise this defect and never could — it is MIR
lowering + codegen.

Fix: `src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs`,
`DispatchMode::Dynamic`. When `find_trait_for_method_on_receiver` returns
`DUCK_DISPATCH_UNSUPPORTED_SLOT` (trait with no `impl Trait for ...` anywhere in
the unit, so no object carries a vtable), the call is no longer lowered to
`MethodCallVirtual` + trap. The receiver is a real object of a concrete class
that HAS the method — exactly the erased (`Any`-receiver) shape the runtime
already resolves by name — so lowering now emits `MethodCallStatic` with the
**bare** method name. Bare is required: `func_name` had been qualified with the
receiver's static type, which for a trait-typed receiver is the TRAIT
(`Backend.label`), and no such function exists.

The codegen trap at `codegen/instr/closures_structs.rs` is kept, unwidened, as
fail-closed defence for any MIR that reaches it with the sentinel by another
route.

Gate: `scripts/check/check-duck-trait-dispatch-jit.shs` (verdict last line,
PASS/FAIL/ERROR, non-vacuous). Fixtures:
`test/01_unit/compiler/codegen/duck_trait_dispatch/`.

| fixture | shape | before (old seed) | after |
|---|---|---|---|
| `impl_ful_trait_receiver.spl` | trait WITH impl (control) | PASS | PASS |
| `erased_any_receiver.spl` | `Any` receiver (control) | PASS | PASS |
| `duck_trait_receiver_single_method.spl` | impl-less trait, 1 method, no args | **rc 132 SIGILL, duck-dispatch diagnostic** | PASS |
| `duck_trait_receiver_multi_method.spl` | impl-less trait, 3 methods (slot index matters), method with args, second trait sharing the method name, class implementing both | **rc 132 SIGILL** | PASS |

Negative control (mandatory, performed): the same gate run against the
pre-change binary `bin/release/x86_64-unknown-linux-gnu/simple` FAILs on both
duck fixtures with rc 132 and the duck-dispatch diagnostic, while both controls
still pass. `PASS — 4 fixture(s) checked` on the fixed build.

**Title correction:** the old title said SIGSEGV. It has not segfaulted for some
time — the sentinel path was already fail-closed, printing a named diagnostic
and executing `trap` (SIGILL, rc 132). That was a large improvement over memory
corruption; theremaining  defect was that the call did not work at all.

## STILL OPEN — native/AOT (see row 17)

Native/AOT does **not** benefit. Measured 2026-08-18 with the fixed compiler:
`native-build` of the duck fixture fails at build time with
`MIR lowering error: unresolved method call: scaled`. This is NOT caused by the
fix: `erased_any_receiver.spl`, which contains no trait at all and is untouched
by this change, fails the same way (5 × `unresolved method call`). **The native
backend has no erased/bare-name method dispatch whatsoever.** That is the whole
of the remaining work, and it is a separate, larger job: implement erased
by-name method resolution in the native lowering path. Until then native is
fail-closed at BUILD time (named error) rather than at runtime.
