# Lane JITLAM — Cranelift JIT lambda/closure ABI scoping

**Date:** 2026-07-29
**Status:** scoping only, no source changes. Deliverable:
`doc/08_tracking/bug/jit_lambda_abi_scoping_2026-07-29.md`
**Guard in place:** `8b72b34f005` (`src/compiler_rust/compiler/src/codegen/jit.rs:111-118`)
demotes any module containing `ClosureCreate` to the interpreter — correct
today, just uncompiled.

## What this lane did

1. Confirmed `codegen/jit.rs` and `codegen/instr/closures_structs.rs` are
   identical to `refs/land/tip` (`eb5be9277e7`) — no concurrent-edit
   contamination in the files this scoping touches, despite a dirty working
   copy elsewhere in the repo (interpreter/memstat/browser-hardening work from
   other sessions, unrelated files).
2. Built `simple-driver` fresh (`cargo build -p simple-driver`), binary
   `src/compiler_rust/target/debug/simple`, **mtime 2026-07-29 03:22:38 UTC**.
3. Ran 3 one-construct probes with `SIMPLE_JIT_TRACE_ADDR=1`: non-lambda fn
   call JIT-compiles (`[jit-addr]` lines, correct `42`); `arr.map(...)` and a
   direct lambda call both demote (no `[jit-addr]`, guard message fires,
   correct interpreted output `[2, 4, 6]` / `40`). Evidence in
   `/tmp/jit_lambda_scoping/`.
4. Read the actual defect end-to-end: `compile_closure_create`
   (`closures_structs.rs:168`) uses bare `rt_alloc` with no `HeapHeader`;
   `compile_indirect_call` (`closures_structs.rs:266`) calls through untagged
   native types; `rt_closure_new` (the correct constructor, with a real
   `HeapHeader`) exists in the runtime and is **already registered** as a JIT
   symbol (`runtime_sffi.rs:525`) but is never called from codegen — so
   sub-task 1 of a real fix may be smaller than feared (swap `rt_alloc` for
   the already-wired `rt_closure_new`), pending confirmation that MIR's
   `capture_offsets` layout matches `RuntimeClosure`'s post-header layout.
5. Found a **second, independent** defect, currently masked by the same
   guard: `.any(pred)`/`.all(pred)` map to `rt_array_any`/`rt_array_all`,
   which are 1-arg truthy-only functions not even declared in
   `runtime_sffi.rs`; the interpreter's `.any`/`.all` DO take a predicate.
   Fixing only the closure-object/tag-boxing defect and then removing the
   guard would silently break `.any(pred)`/`.all(pred)` under JIT. Must be
   fixed together or the guard must be narrowed (not removed) until it is.
6. Found the **LLVM AOT backend has the identical closure-ABI defect**
   (`codegen/llvm/functions/objects.rs:218`,
   `codegen/llvm/functions/calls.rs:2570`) with **no guard at all** — AOT
   binaries using lambdas are exposed today with no interpreter fallback.
   Out of this task's scope; flagged for a follow-up bug.

## Recommended sequencing (detail in the doc)

1. Confirm `capture_offsets` vs `RuntimeClosure` layout (read-only, not done
   in this pass — first concrete implementation step).
2. Fix `compile_closure_create` + `compile_indirect_call` together (only real
   codegen surface: 2 functions, `closures_structs.rs`).
3. Narrow the `8b72b34f005` guard to only demote `.any`/`.all`-with-predicate
   modules, so map/filter/find/direct-call lambdas start JIT-compiling.
4. Add predicate-taking `.any`/`.all` runtime functions + arity dispatch.
5. Drop the narrowed guard.
6. File the LLVM AOT parity gap separately.

## Not done (explicitly out of scope for this lane)
- No source file was modified.
- No fix implemented or attempted.
- LLVM AOT defect not fixed, only flagged.
