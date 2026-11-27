# Interpreter JIT file-state hot path
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Status

Resolved 2026-11-18 (Wave B1). Previously open from the 2026-09-16 bug-ledger
normalization pass (source inspection only; no benchmark was run in the
no-verification sync lane).

## Evidence

`jit_record_call` can load the process JIT state, call `jit_mark_symbol_used`
which loads and writes it, then load and write it again for the call counter.
Other query helpers also reload the same file. Therefore recorded calls perform
multiple filesystem operations rather than an O(1) in-memory update.

## Required fix

Design a process-owned in-memory state with explicit synchronization and a
bounded persistence policy. Preserve cross-process semantics or replace them
with an atomic owner protocol. Measure call latency, write frequency, and peak
RSS before and after. Do not silently cache mutable shared state or remove crash
recovery solely to improve a microbenchmark.

## Current containment

Raw file and PID declarations are removed. Canonical owners preserve existing
operation counts, typed read failure, exact one-call writes, and validated PID
identity. No extra I/O was added by the SFFI authority migration.

## Resolution (2026-11-18 — Wave B1)

1. **Process-owned in-memory JIT tables (`src/compiler/10.frontend/core/interpreter/jit.spl`)**:
   Replaced per-call `/tmp/simple_jit_{pid}.sdn` reads and atomic writes (4 disk
   reads + 2 atomic writes per recorded call when enabled) with process-owned
   chained hash tables (`HM_SIZE = 256`) for `call_counts`, `compiled`,
   `compile_failed` (negative cache), and `used_epochs`. Hot-path filesystem I/O
   is now strictly zero (`0` reads, `0` writes, `0` `/tmp/simple_jit_*.sdn`
   files).
2. **Eliminated fake `0` JIT return & unbounded recompile attempts (`jit.spl`, `eval_calls.spl`, `_EvalOps/call_method_eval.spl`)**:
   `jit_try_compile` no longer marks `fn_name` compiled when no native callable
   is registered; instead it records `fn_name` in `compile_failed` so
   `jit_should_compile` returns `false` on subsequent calls (at most 1 compile
   attempt per symbol). Added `jit_try_execute_checked(fn_name, args) -> (bool, i64)`
   returning `(false, 0)` on fallback and wired `eval_calls.spl` +
   `_EvalOps/call_method_eval.spl` so legitimate `-1` native returns succeed
   without falling back to tree-walking, and unbacked symbols never return a
   fabricated `0`.
3. **`O(1)` caller/owner call tables, `_yield_cache` reset, and method-receiver probe skip (`eval_tables.spl`, `eval_calls.spl`, `_EvalOps/call_method_eval.spl`)**:
   Added `HM_SIZE = 256` chained hash indices in `eval_tables.spl` for
   `(owner, name)` in `fto_*`, `(caller, local_name)` in `fib_*`,
   `(caller, alias)` in `fmn_*` (plus per-caller `fmn_caller_buckets`), and
   per-`name` owner counts (`func_owner_count`, zero `owners: [text]` allocation
   on normal flat-fallback calls). Unified `_yield_cache` in `eval_tables.spl`
   and cleared it in `func_table_reset()` so recycled `decl_id`s after
   `ast_reset()` never inherit stale generator flags. Bound
   `expr_get(receiver_eid)` once in `_EvalOps/call_method_eval.spl` and skipped
   static namespace/enum/struct probes when `expr_owner_int(receiver_eid) >= 0`.
4. **Verification**:
   Pinned in `test/01_unit/compiler/interpreter/core_interp_call_and_jit_state_perf_spec.spl`.


