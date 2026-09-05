# JIT: direct `Engine2D.create_with_backend_fast` from flat main silently truncates (trait dispatch)

- **Filed:** 2026-09-02
- **Status:** OPEN — observation, needs a minimal repro reduction and a codegen
  owner; do NOT paper over by de-JITing the path
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
