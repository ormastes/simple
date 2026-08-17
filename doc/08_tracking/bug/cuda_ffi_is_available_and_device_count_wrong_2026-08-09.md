# `CudaFfi.is_available()` false and `device_count()` 0 on a host with two working GPUs

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

**Filed:** 2026-08-09 (stream F4)
**Subject:** `src/lib/nogc_sync_mut/gpu/engine2d/ffi_cuda.spl`
**Host:** Linux x86_64, NVIDIA RTX A6000 + NVIDIA TITAN RTX,
`libcuda.so.1 -> libcuda.so.580.126.16`

## Summary

On a host where CUDA demonstrably works, `CudaFfi` reports it as
unavailable and reports zero devices — while `init()`, on the very same
object, succeeds by really calling `cuInit` through the real driver. The
object contradicts itself.

Measured (`bin/simple run`, Dynamic mode, `create_dynamic()`):

| call | result | expected |
|---|---|---|
| `create_dynamic()` | non-nil (dlopen OK) | non-nil |
| `api_name()` | `CUDA Driver API` | ok |
| `init()` | **true** | true — real `cuInit(0)` returned CUDA_SUCCESS |
| `is_available()` | **false** | true |
| `device_count()` | **0** | 2 |

`nvidia-smi` on the same box lists two devices.

## Defect 1 — `is_available()` calls `cuInit` with the wrong arity

```
fn is_available() -> bool:
    match self._mode:
        case Static: rt_cuda_available() != 0
        case Dynamic:
            if self._dyn_lib != nil:
                val result = self._dyn_lib.call0("cuInit")   # <-- call0
                result == 0
```

`cuInit` takes one argument (`unsigned int Flags`). `is_available()`
invokes it through **`call0`** — no argument — so the flags register holds
garbage and the driver returns a non-zero error, which is then read as
"CUDA unavailable".

`init()`, four lines below, gets it right and is the proof:

```
case Dynamic:
    val result = self._dyn_lib.call1("cuInit", 0)            # <-- call1
    result == 0
```

Same function, same object, opposite answers. `call0` -> false,
`call1(…, 0)` -> true.

## Defect 2 — `device_count()` returns 0 with two devices present

`cuDeviceGetCount(int *count)` writes its result through an **out
pointer**. The raw `call0..call4(i64...)` FFI used here returns only the
CUresult status code and has no way to marshal the out parameter, so the
count is never read back and 0 is reported.

This is the same structural limitation that `VulkanFfi` handles honestly:
that class refuses such operations and records them via
`rejected_op_count()` / `last_rejection()` rather than returning a
plausible-looking wrong value. `CudaFfi` has no such ledger and returns a
silent, wrong 0 — a number a caller cannot distinguish from "no GPUs".

## Defect 3 (related) — `synchronize()` returns true when the extern is missing

Static mode, same file:

```
sync=true
```

was printed immediately after the runtime logged

```
ERROR rt_interp_call error: unknown extern function: rt_cuda_synchronize
```

A missing extern must not surface as success. This is a fail-open on the
Static path, which under the interpreter has no `rt_cuda_*` externs at all
(`is_available`/`init`/`device_count` all report false/0 there for that
reason, not because of the hardware).

## Reproduce

```bash
cat > probe.spl <<'EOF'
use std.nogc_sync_mut.gpu.engine2d.ffi_cuda.{CudaFfi}
fn main():
    val d = CudaFfi.create_dynamic()
    if d == nil:
        print("NIL"); return
    print("is_available=" + d.is_available().to_text())
    print("init=" + d.init().to_text())
    print("device_count=" + d.device_count().to_text())
EOF
SIMPLE_MODULE_LIMIT=4000 bin/simple run probe.spl
```

## Spec status

`test/01_unit/lib/gpu/engine2d/ffi_cuda_spec.spl` (rewritten by F4)
deliberately does **not** assert `is_available()` or `device_count()`.
Asserting the currently-observed `false` / `0` would bake these defects in
as expected behaviour. It asserts `init()`, which is the call that really
reaches the driver. Once this bug is fixed, add:

```
expect(ffi.is_available()).to_equal(true)
expect(ffi.device_count()).to_be_greater_than(0)
```

## Note on scope

Distinct from the seven defects listed in
`gated_specs_are_tautology_shells_2026-08-09.md`. That doc's item 1
(`feature/usage/cuda`, "`expected -3 to be greater than 0`") is plausibly
the *same* root cause as Defect 2 here — an out-pointer count call returning
a bare CUresult. Whoever fixes that should check this file too.

---

## 2026-08-17 — REPRODUCED and FIXED (GPU slice worker E)

Classified by CONTENT against current source, not by commit ancestry.

### Root cause (confirmed live before the fix)

`src/lib/nogc_sync_mut/gpu/engine2d/ffi_cuda.spl`, Dynamic-mode arms:

| line | call | real C signature | what was returned |
|------|------|------------------|-------------------|
| :131 | `call0("cuDeviceGetCount")` | `cuDeviceGetCount(int* count)` | the `CUresult`, not the count |
| :142 | `call2("cuCtxCreate", 0, device)` | `cuCtxCreate(CUcontext*, unsigned, CUdevice)` | the `CUresult`; also the wrong ARITY (3 params, 2 passed) |
| :175 | `call1("cuMemAlloc", size)` | `cuMemAlloc(CUdeviceptr*, size_t)` | the `CUresult`, not the device pointer |
| :106 | `call0("cuInit")` | `cuInit(unsigned int Flags)` | called with ZERO args — the flags register was left undefined |

The mechanism is a single shared defect, not four: **`DynLib` has no
out-parameter marshalling at all.** `src/lib/nogc_sync_mut/sffi/dynamic.spl`
exposes only `call0`/`call1`/`call2`/`call3`/`call4`/`call_n` (`:66`-`:116`),
every one of which returns the callee's raw `i64` RETURN value. There is no
API to pass a pointer and read back what the callee wrote into it.

This is a textbook silent-wrong-result. For all three of these CUDA APIs the
SUCCESS status is `0`, and `0` is also each caller's "it failed" sentinel:

- `device_count()` returned `0` — read as "no GPUs" on a two-GPU host;
- `ctx_create()` returned `0` after a *successful* create, which its own
  `if ctx < 0: 0 else: ctx` contract treats as failure;
- `mem_alloc()` returned device pointer `0` after a *successful* allocation.

Nothing crashes, nothing warns, and the process exits 0.

`is_available()` had a second, independent bug layered on top: even a correct
`cuInit` returning `CUDA_SUCCESS` only proves the driver loaded, not that any
device exists — so "available" and "0 devices" could both be true at once.

### Fix

The static path is a real, correct implementation that marshals the out
parameters properly — verified in
`src/compiler_rust/runtime/src/cuda_runtime.rs:1398` (`rt_cuda_device_count`
-> `get_device_count()`) and `:1404` (`rt_cuda_available`). The Dynamic-mode
arms for the three out-param entry points now route to those static externs,
each with a comment naming the out-param reason so the pattern is not
reintroduced. `is_available()` now calls `cuInit` via `call1` with the
required flags argument and additionally requires `device_count() > 0`.

Deliberately NOT done: adding out-parameter marshalling to `DynLib`. That is
the general cure, but `src/lib/nogc_sync_mut/sffi/**` is outside this slice's
ownership. Filed as the real follow-up below.

### Specs

- Reproducing:
  `test/01_unit/lib/gpu/engine2d/ffi_cuda_out_param_marshalling_spec.spl`
  — pins dynamic/static agreement on device count, forbids the incoherent
  "available but zero devices" state, and forbids a negative count (a leaked
  `CUresult` can be a negative error code).
- Similar-problem detection:
  `test/01_unit/lib/gpu/engine2d/ffi_out_param_via_return_value_detection_spec.spl`
  — source-level guard over ALL five GPU FFI dispatchers (cuda, opencl,
  vulkan, rocm, intel) against 15 known out-parameter C symbols x 6 `DynLib`
  call forms, so a NEW out-param call added to any of them fails here instead
  of shipping. Includes a non-vacuity check (the corpus must be non-empty)
  and a self-test that the matcher recognises the historical defect line.
  The detection spec is source-level on purpose: the behavioural spec can only
  exercise backends this host actually has, and a GPU-less host exercises none.

### Follow-up (not fixed here)

`DynLib` cannot express an out parameter. Every dynamic-mode binding to any C
API that returns through a pointer is unsafe by construction, GPU or not. The
detection spec fences the GPU dispatchers; the underlying gap in
`src/lib/nogc_sync_mut/sffi/dynamic.spl` remains open and needs an owner.
