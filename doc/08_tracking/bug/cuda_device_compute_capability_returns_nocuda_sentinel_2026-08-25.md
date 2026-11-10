# `cuda_device_compute_capability` returns the no-CUDA sentinel (-3) on a working CUDA host (2026-08-25)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** OPEN — LIVE, re-confirmed in source 2026-11-11 (lane ne5) — `test/03_system/acceptance/gpu_cuda_programming_acceptance_spec.spl` is
deliberately RED on this (1 of 5 examples).
**Binary:** deployed seed `bin/release/x86_64-unknown-linux-gnu/simple`. **Host:** 2 NVIDIA GPUs.

## Symptom
In one process, on one binary, the neighbouring calls succeed and this one does not:

```
PROBE avail=true init=0 count=2
PROBE name0=[NVIDIA RTX A6000] cc0=-3
```

`-3` is the runtime's "built without the `cuda` feature" sentinel. It cannot be true here:
`cuda_available()`, `cuda_init()`, `cuda_device_count()` and `cuda_get_device_name(0)` all went
through the real driver in the same process moments earlier.

## Why it matters
The value is returned as a plain `i64` (packed, e.g. `86` for sm_86), so `-3` is not distinguishable
from a capability by type. Any code that selects a kernel variant or a PTX `.target` from this
number silently picks the wrong one — the same silent-wrong-answer class as the unbacked externs
fixed in `8a291217121`.

## Where to look
`rt_cuda_device_compute_capability` in the interpreter's extern dispatch
(`compiler/src/interpreter_extern/gpu.rs`): the sibling entries have a dlopen fallback that reaches
the driver, and this one appears to fall through to the `-3` stub. Same shape as the known
`rt_cuda_memcpy_htod_array` gap noted while adding streams/events.

## Reproduce
```
SIMPLE_CUDA_TEST=1 bin/simple test test/03_system/acceptance/gpu_cuda_programming_acceptance_spec.spl
```
→ `Results: 5 total, 4 passed, 1 failed`, failing example
`discovers the machine's GPUs and what they are, with no CUDA toolkit installed`.


## 2026-11-11 addendum (lane ne5)

**Status: LIVE — confirmed in current source; keep OPEN.**

Triage on release/1.0.0 tip:

- `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:1382-1392`
  (`rt_cuda_device_compute_capability_fn`): the `#[cfg(not(feature = "cuda"))]`
  branch STILL returns the `-3` sentinel with no dlopen fallback, while its
  siblings in the same file (`rt_cuda_device_get_fn`, `rt_cuda_device_name_fn`,
  `rt_cuda_device_identity_fn`) all reach the real driver through
  `get_cuda_dl()`. Exactly the gap named in this doc's "Where to look".
- `get_cuda_dl()` (`gpu.rs:505`) and the `CudaFns` table (`gpu.rs:520`) already
  carry the capability symbol, so the sibling-shaped fix is a few lines.
- The pure-Simple runtime side lists `rt_cuda_device_compute_capability` in
  its required CUDA-provider dynload table (`src/runtime/runtime_dynload.c:200`)
  and `src/lib/gc_async_mut/cuda/mod.spl` re-exports it — the gap is the seed
  interpreter's not-built-with-cuda path, which is what a deployed seed
  answers.

Not fixed here: this lane is barred from cargo/rustc and entry-closure native
builds, so a `gpu.rs` edit cannot be rebuilt into the tracked seed binary, and
this Windows host has no NVIDIA device to run the acceptance spec against in
any case. Grant: add the `get_cuda_dl()` fallback for `device_compute_capability`
in `gpu.rs` (mirror the sibling entries, mapping a failing call to a negative
driver rc rather than the `-3` build-sentinel so the sentinel keeps meaning
"built without cuda"), rebuild/redeploy the seed, then verify with
`SIMPLE_CUDA_TEST=1 bin/simple test test/03_system/acceptance/gpu_cuda_programming_acceptance_spec.spl`
on a CUDA host (expect 5/5).
