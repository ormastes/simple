# `cuda_device_compute_capability` returns the no-CUDA sentinel (-3) on a working CUDA host (2026-08-25)

**Status:** OPEN — `test/03_system/acceptance/gpu_cuda_programming_acceptance_spec.spl` is
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
