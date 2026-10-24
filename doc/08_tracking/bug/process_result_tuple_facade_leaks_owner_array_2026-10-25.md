# Process/cpuid raw-block facades leak per call

Status: OPEN (P3)

## Summary

The pure-Simple native lanes destructure a tuple result by loading words of a
raw block, so the C facades in `src/runtime/runtime_native.c` repack the
owner's registered result into an `rt_alloc`'d block:

- `rt_process_result_to_tuple` (used by `rt_process_run_tuple`,
  `rt_process_run_timeout_tuple`, `rt_process_run_bounded_tuple`,
  `rt_process_run_bounded_bytes_tuple`) copies slots out of the owner's
  `SplArray*` and never frees that array. Only
  `rt_process_run_owned_observed_bounded_text` calls `rt_array_free` on it.
- `rt_cpuid_tuple_block` allocates a fresh block per call.
- Nothing frees the returned block: the word-load destructure reads it and
  drops it.

The Rust twins in `env_process.rs` (`raw_result_block` via `Box::into_raw`,
plus the intermediate `rt_tuple_new` owner tuple) leak identically.

Cost: one result array plus one 24-32 byte block per spawn / cpuid call. Not a
regression of `work/p3fix-spawn4`: the LLVM lane always used these facades; the
Cranelift lane now does too.

## Fix direction

Free the owner array in `rt_process_result_to_tuple` once slots 0/1 are
transferred (they stay referenced by the block), mirroring the owned-observed
facade; give tuple-result blocks an owner in the destructure lowering (or
scope-free them) so the block itself is reclaimed.
