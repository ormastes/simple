# JIT: direct `Engine2D.create_with_backend_fast` from flat main silently truncates (trait dispatch)

- **Filed:** 2026-09-02
- **Status:** FIXED 2026-11-11 (lane ne12, verification-limited) — root trait-dispatch
  cause fixed in seed 2026-10-20 (6da314289493 + efd9c18cbdaf; was
  verification-pending on a redeployed seed); filed program shape completes fully
  under JIT on fresh seed 46fe8f6b6def (Windows non-Metal fallback path); the
  Darwin/Metal lane itself was not re-runnable on this host
- **Platform:** aarch64-apple-darwin, seed driver, `gui,metal,runtime-symbol-table`

## Symptom

Under the JIT lane this program prints only `start` and exits 0:

```
use gpu.engine2d.engine.{Engine2D}
fn main():
    print "start"
    var engine = Engine2D.create_with_backend_fast(320, 240, "metal")
    print "created backend={engine.backend_name()}"
    engine.clear(0xFF141414u32)
    print "cleared ok"
    engine.shutdown()
```

`SIMPLE_EXECUTION_MODE=interpret` prints all four lines. The JIT run produces
no error, no fallback, no trap — it silently never executes anything after the
static call. This is exactly the "silent miscompile that links and runs to
completion" shape `jit_strict_coverage_gap_2026-07-30.md` says the strict gate
can never catch.

## History in this lane

- Before the 2026-09-02 runtime-symbol-table fix, the same probe died with
  SIGTRAP (`Trace/BPT trap: 5`, ud2) — the documented
  `class Engine2D with DrawIrRenderTarget` duck-dispatch-into-ud2 class
  (`native_with_trait_impl_no_vtable_duck_trap_2026-07-28.md`).
- After the symbol-table fix, the same closure stops trapping and silently
  truncates instead. Behavior changed; the root trait-dispatch defect is
  unchanged.
- The full showcase entry (`main_2d_gpu.spl`) JITs and produces correct output
  (verified visually), so the defect is shape-specific, not path-wide.

## Not this

- Not the unresolved-import guard: the probe's symbols all resolve; the guard
  passes it either way.


## Sibling observation (same lane, 2026-09-02): composition-mutation heap corruption

While the guard fix was in place, adding ANY new batch-manipulation code to
`showcase_composition` (`src/app/ui_showcase/showcase_core.spl`) — either an
in-place `comp.batches[0]` struct copy/field-write/write-back or a
prepend-batch rebuild — made `main_2d_gpu.spl` on Metal crash intermittently
(~1 in 3 runs) with fatal heap signals:

- `Abort trap: 6` — lldb: `___BUG_IN_CLIENT_OF_LIBMALLOC_POINTER_BEING_FREED_WAS_NOT_ALLOCATED`,
  called from JIT code frames (`JitCompiler::call_i64_void` caller), OR
- `Bus error: 10` with no panic log.

Pristine sources passed 3/3 in the same minutes; a standalone probe of the
identical copy/mutate/write-back op pattern on `DrawIrBatch` values passed
under JIT — so the corruption is layout/timing-sensitive (which functions
JIT-compile and where allocations land), not a deterministic miscompile of
that one function. The ground-rect injection was reverted; the Metal lane
keeps `engine.clear` per frame instead. Root cause NOT found; treat any new
JIT-lane heap-corruption crash in this app as this family until reduced.

## Triage 2026-11-11 (lane ne12, seed-smoke on fresh seed 46fe8f6b6def)

**Verdict: FIXED (verification-limited) — kept honest about what was re-run.**

Root cause: the filed silent truncation sat on the same trait-dispatch defect
as `native_with_trait_impl_no_vtable_duck_trap_2026-07-28` (`class Engine2D
with DrawIrRenderTarget` — no vtable registered, duck-dispatch slot). That
doc records: fix implemented 2026-10-20 in the seed
(`6da314289493` "trait dispatch for `class X with Trait` and Option<Trait>
payloads" + `efd9c18cbdaf` single-trait restriction; both `DrawIrRenderTarget`
conformers are single-trait mixin classes), status
"fix-implemented-verification-pending: needs a redeployed seed + native build
of the Draw IR executor". Today's fresh seed (build-commit 46fe8f6b6def,
2026-11-11) IS the redeployed seed that verification was waiting for.

Seed-smoke evidence (this lane, Windows host): the filed program shape
(flat `main`, direct static `Engine2D.create_with_backend_fast(320, 240, ...)`,
then `backend_name()`, `clear`, `shutdown`) now completes fully under the
DEFAULT JIT lane — all four lines printed, exit 0, no truncation, no trap:

```
JIT:        start / created backend=cpu / cleared ok / shutdown ok
interpreter: start / created backend=cpu / cleared ok / shutdown ok
```

(`build/review/ne12/row5_engine2d_shape.spl`; "cpu" exercises the documented
non-Metal fallback of `create_with_backend_fast`, which forwards to
`create_with_backend` — the Metal-only fast path is Darwin-only.)

**Verification limit:** the exact filed lane (aarch64-apple-darwin, Metal,
`create_with_backend_fast(..., "metal")`) cannot execute on this Windows host —
Metal does not exist here, and this lane is forbidden from native builds. The
Darwin JIT+Metal re-run remains for a macOS lane; if it still truncates there,
reopen with the macOS repro. The sibling heap-corruption observation in this
doc (composition-mutation crash family) was explicitly "treat any new crash in
this app as this family until reduced" — no new instance was observed in this
lane's runs.

Not carried by seedfix A (fa6939eb4b9e is JIT tuple unbox; unrelated to
trait/vtable dispatch).
