# Windows: owned observed process capsule unusable from seed-built tools

- **Date:** 2026-09-25
- **Status:** OPEN (option A of the owner decision). Option B is in place as the workaround.
- **Area:** runtime / seed codegen / `std.nogc_sync_mut.io.resource_scope`

## What was measured

- **Who compiles the tools.** The stage-2 `simple_cli` / `simple_test_runner` on Windows come out of the
  seed's embedded Rust native pipeline (LLVM backend). The pure-Simple `MirToLlvm` path does not
  build them. The facade added in #1573 (`core_codegen.spl`, `rt_process_run_owned_observed_bounded_text`)
  therefore never reached them.
- **Two ABI mismatches** in the seed's call to `rt_process_run_owned_observed_bounded_value`:
  1. **Argument shape.** The `cmd: text` argument is passed as one word, while the C owner
     (`runtime_process_owned.c`) takes `(cmd_data, cmd_len, ...)`.
     - Adding the symbol to the seed's `process_c_runtime_arg_indices` fixes the alignment, and the
       child then spawns.
     - That change is branch `work/win-owned-process-seed-abi-20260925`, `5dfd0eebb94`, not landed.
  2. **Result shape.** The C owner returns a raw `rt_alloc`'d 3-word tuple (the pure-Simple tuple
     ABI). The seed destructures a tuple result as a runtime array, so it logs `rejected invalid array
     handle` and the caller still sees exit -1.

## Workaround in place (option B)

- `process_run_observed_bounded` goes through `_legacy_process_fallback` when
  `host_is_windows_host()` is true.
  - That calls `rt_process_run_bounded` (`runtime_process.c`: CreateProcess, job object, pipes).
  - Its seed call shape already works.
- **Cost:** resource evidence is `Unavailable` on Windows. The test RSS cap is still enforced by the
  runner's Job-Object guard.

## Option A (this todo)

1. **An array-returning wrapper.** Add one for the owned capsule (e.g.
   `rt_process_run_owned_observed_bounded_array`). It returns
   `[stdout, stderr, fields]` as a runtime array, the seed tuple ABI that `rt_process_run_bounded`
   already uses.
   - Route the seed to it via `process_c_runtime_arg_indices`.
   - Route the pure-Simple backend to it via a `translate_call` rewrite, replacing the `_text` facade.
2. **Rust twins.** The owned-process family has none: `rt_process_run_owned_*` and
   `rt_process_owned_v3_*` are C-only in `scripts/check/rt_dual_implementation_baseline.txt`. The new
   wrapper and the family need twins so `check-rt-dual-implementation-ratchet.shs` stays at 0 new.
3. **Remove the Windows branch** in `process_run_observed_bounded` once a native probe shows the
   capsule returns exit code, stdout and a non-`Unavailable` evidence quality on Windows.

**Done when:** that probe passes and the stage-2 `compiler_bootstrap_tests` row reports resource
evidence on Windows.
