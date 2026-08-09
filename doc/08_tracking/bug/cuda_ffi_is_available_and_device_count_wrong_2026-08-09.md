# `CudaFfi.is_available()` false and `device_count()` 0 on a host with two working GPUs

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
