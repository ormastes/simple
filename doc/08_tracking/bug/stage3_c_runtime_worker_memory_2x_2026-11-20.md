# Stage 3 shard worker uses 2x Stage 2's memory: codegen pool translates IR unscoped (2026-11-20)

- **ID:** stage3_c_runtime_worker_memory_2x_2026-11-20
- **Priority:** P1 (Stage 3 -> Stage 3 shard worker thrashes at its 40G cgroup cap)
- **Status:** fix landed in source; RSS after the fix needs a Stage 3 built from this source
- **Related:** `codegen_module_memory_not_freed_per_module_2026_11_02.md` (same
  defect, already fixed on the serial lane), `stage3_transient_scope_object_cap_panic_2026-11-20.md`

## Symptom
Source 1f332b24464, 14-shard MIR split, about 115 modules per shard worker
(logs under `boot-fable-lane-scripts/diaglink/s3i2/`):

| run | producer | backend | codegen lane | worker peak |
|---|---|---|---|---|
| `p3i22c` | Stage 2 (Rust runtime) | `cranelift` | `concurrency=1 (serial lane in this process: backend session owns codegen)` | 19.4G |
| `s3s3i22c` | Stage 3 (C runtime, core-c-bootstrap) | `llvm` | `concurrency=2 (process pool: 2 llc workers, IR translation serial in this process ...)` | 39.6G (thrashing at the cap) |

## The comparison was not like for like
The two runs used different backends (`integ22c_p3s3.sh`: `BACKEND=cranelift`
for p3i22c and `BACKEND=llvm` for s3s3i22c), so they took different codegen
lanes. The extra memory comes from the lane, not from the C runtime.

## Where the memory grew (`s3s3i22c.mem.log.saved`)
- parse/HIR/MIR: up to about 19.5G, the same envelope as Stage 2 (16-19G per worker).
- `native_compile`: 19.5G -> 28.2G -> 37.7G -> 39.3G while the log prints
  `[NATIVE] codegen-pool: ir N/115`. It then plateaus at the cap.

That is about 170 MB retained per module, for 115 modules.

## Root cause
`_driver_codegen_pool_emit_v1` (`80.driver/driver_aot_native_output.spl`)
calls `llvm_module_ir_to_path_v1` (`70.backend/backend/backend_helpers.spl`)
once per module in the parent process. That function did the following with
**no transient scope**:
- storage-projection lowering
- the backend MIR optimization copy
- IR translation, producing the whole module's IR text
- the IR file write

Nothing in the C or Rust runtime frees an unscoped object (no GC and no
refcount on this path), so every module's IR text and translator scratch stayed
live for the whole shard.

The serial lane already frees the same work per module, through:
- `compile_llvm_module_to_object_path`, which scopes optimization and promotes the MIR;
- `llvm_compile_module_direct_to_path`, which scopes translation and emission.

That was the fix for `codegen_module_memory_not_freed_per_module_2026_11_02`.
The process pool (step 5 P2) was added later and never got the scope.

## Hypotheses ruled out
- **(a) Transient-scope objects not freed at scope exit.** The growth happens
  in a phase that opens no scope at all on this lane.
- **(b) Per-object overhead about 2x in the C runtime.** Through MIR, both
  runtimes use the same memory.
- **The `[transient-scope] WARNING scope 42578 tracks more than 16777216 objects` line** (the only one in
  the log). It is printed during MIR lowering, before codegen. The tracking list
  is 12 bytes per entry (about 0.4 GB at 2^25 entries), so it does not explain
  20G. It is a separate, large per-module MIR scope.

## Fix
`llvm_module_ir_to_path_v1` now opens one transient scope per module around
storage lowering, optimization, translation and the IR write. The scope follows
the serial lane's qualified pattern:
- Warm `bootstrap_llvm_name_index_ensure()` before the scope opens.
- If the scope is refused, warn and translate unscoped.
- After pausing the scope:
  - call `reset_provider_report()`;
  - retain the bootstrap string-global cache;
  - promote only a non-empty failure reason.
- `SIMPLE_CODEGEN_MODULE_SCOPE=0` keeps the old unscoped lane.

`llc` still runs in child processes, outside the scope.

**Immediate workaround without a rebuild:** `SIMPLE_NATIVE_CODEGEN_POOL=0`
sends `--backend llvm` through the scoped serial lane.

## Rebuild impact
This is compiler `.spl`, not runtime C. A Stage 3 produced at Phase 3 from this
source carries the fix. Stage 2 never takes the pool lane with
`--backend cranelift`, so it is unaffected. Stage 3 binaries that are already
running do not have the fix.

## Verification
- **Red/green on committed source:**
  `sh test/01_unit/compiler/backend/llvm_codegen_pool_ir_scope_source_contract_test.shs`.
  On base it fails with `FAIL: llvm_module_ir_to_path_v1 lacks:
  llvm_codegen_module_scope_enabled_v1()`; with the fix it reports `PASS`.
- **Behavioural spec (not yet run):** a new case, `does not grow the heap per
  module across N codegen-pool IR emissions`, in
  `test/01_unit/compiler/backend/llvm_codegen_module_scope_default_spec.spl`
  compares heap growth over 16 emissions, scoped vs `=0`. No runnable full-CLI
  binary was deployed on this host, so it is pending.
- **Expected RSS after the fix:** the MIR-phase floor, about 19-20G per
  worker, the same as Stage 2.
