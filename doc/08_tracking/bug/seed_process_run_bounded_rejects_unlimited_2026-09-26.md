# Seed interpreter `rt_process_run_bounded` rejects `-1` (unlimited), so every std `process_run` fails on Windows under the seed

- **Filed:** 2026-09-26
- **Status:** FIXED in source (seed interpreter). The frozen stage-2 authority seed
  used by the delegated bootstrap lane keeps the old behaviour until it is
  rebuilt and re-admitted.
- **Area:** `src/compiler_rust/compiler/src/interpreter_extern/system.rs`
  (`rt_process_run_bounded`)
- **Host:** Windows 11, x86_64-pc-windows-msvc

## Symptom

On Windows, every std `process_run` / `run_process` call made from a spec run
under the seed interpreter aborts the example with:

```
runtime: rt_process_run_bounded: max_output_bytes must be a non-negative integer
```

Seen in `test/01_unit/compiler/bootstrap/llvm_aggregate_shared_binding_contract_spec.spl`.
It passed in the bootstrap46 lane at `34d23c5d848` and fails 0/2 at
`9bbc60013c6`.

## Cause

`dac914d9306` (2026-09-26) routed std `process_run` on Windows
(`src/lib/nogc_sync_mut/io/process_ops.spl`, `src/lib/nogc_sync_mut/io_runtime.spl`)
to `rt_process_run_bounded(cmd, args, 0, -1)`, to avoid the C
`rt_process_run` exit-0 defect
(`windows_rt_process_run_always_exit_zero_2026-09-26.md`). In the C runtime
owner (`runtime_process.c` `win_process_run_capture`), `-1` means unlimited.
The seed interpreter's implementation accepted only `>= 0`. The two lanes
disagreed on the contract.

## Fix

The seed now accepts `-1` as unlimited. It maps it to `i64::MAX` rather than
`usize::MAX` so that `read_bounded`'s `(max_bytes + 1) / 2` cannot overflow.
Values below `-1` are still rejected, matching C. Regression test:
`system::tests::process_run_bounded_accepts_minus_one_as_unlimited` fails
without the fix and passes with it.

## Remaining

The delegated stage-2 lane pins the frozen seed by sha256, so
`llvm_aggregate_shared_binding_contract_spec` stays red there until the seed is
rebuilt and re-admitted. The alternative is a library-side change that passes
a bound both lanes accept. No single value works today: the C owner
preallocates `limit` bytes for any finite limit.
