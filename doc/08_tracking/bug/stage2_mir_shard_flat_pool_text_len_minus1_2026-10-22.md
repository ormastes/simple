# Stage2 MIR shard: flat-pool encode of MIR artifact sees invalid text handle (rt_string_len == -1), worker stack-overflows

Date: 2026-10-22
Lane: bootstrap-from-scratch, stage2 gate (attempt 36)
Tree: release/1.0 @ a868480a973 (includes PR #4162 HIR crash fixes)

## Symptom

`candidate_frontend_smoke: p2_add-build failed (raw rc=125)` at the stage2
sanity gate. The stage2 candidate compiles `p2_add.spl` through HIR
successfully, then fails while serializing the MIR artifact:

```
flat pool encoder string builder append failed site=text.value item=0 input_length=-1 result=0
[mir-shard] owner=0/1@0 status=CRASH exit=-1073740791 claimed=0 sealed=0 finished=false
[mir-shard] inventory incomplete rows=-1 policy_fail_fast=false
[mir-shard] completed_workers=0 failed_workers=2 failed_modules=0 unfinished=-1
[mir-shard] outcome=fallback exit=1 ... falling back to in-process unsharded MIR
error: native-build worker exited with code -1073740791.
... (fallback, in-process) ...
error: native-build worker terminated with Windows native status 0xC0000409 (fail-fast termination)
```

exit=-1073740791 == 0xC00000FD (stack overflow) in the MIR shard worker.
The subsequent 0xC0000409 is the in-process fallback dying on the same
corrupt state.

## What the diagnostic proves

`flat_pool_builder_push` (src/compiler/10.frontend/core/flat_pool_codec.spl:454)
panics with this message only when `rt_string_builder_push` rejects the
append, and then reports `rt_string_len(value)` of the rejected input.
`input_length=-1` means the `value` text handle is INVALID (foreign /
dangling) at encode time — `rt_string_len` returns -1 for it.

- site=3 (`text.value`), item=0: the FIRST element of the FIRST text pool
  of the MIR artifact is corrupt.
- The encoder itself is unchanged and was reliable before; this is value
  corruption upstream of encoding, not an encode-logic bug.
- HIR phase is clean on this tree: `[hir-shard] done shard=0/1 lowered=1`,
  `failed_workers=0`, `hir-cache stores=1 selfchecked=1`. The corruption
  appears in (or before) MIR artifact pool construction.

## Suspects

1. Interaction between the new dict-literal-typed `HirLowering` fields
   (8a447adbdb4 "declare HirLowering dict fields with literal types, not
   aliases") and the MIR artifact handoff: a field that previously rode an
   alias type may now be stored/extracted differently, leaving a non-text
   word in a text pool.
2. MIR-side pool construction storing a garbage/foreign handle into a text
   pool for values it never validated (module names, string literals,
   symbol spellings). p2_add is tiny (a single `print` of an integer add),
   so the first text pool is likely string-literals or symbol/module names.

## Repro (deterministic, ~10s)

```
CAND=.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe.rejected
env SIMPLE_HIR_SHARDING=0 SIMPLE_LIB=$PWD/src SIMPLE_BOOTSTRAP= SIMPLE_FRONTEND_CACHE=0 \
  "$CAND" native-build --entry src/compiler/bootstrap_admission/p2_add.spl \
  --runtime-bundle core-c-bootstrap --entry-closure --mode one-binary \
  -o /tmp/p2_add_probe.exe
```

(shard-off repro hits the same path via the in-process fallback.)

## Notes

- The refusal instrumentation from d9fd506b9b9 / a868480a973 works: the
  refusal print appears and is flushed.
- `[frontend-cache] store failed: cannot write under .../stage2-tmp/...`
  (`dir_create_all=true`) appears in the same window; modules reparse.
  Looks like a benign tmp-dir IO race, noted separately from this defect.
- Not yet verified on: any tree after a868480a973.
