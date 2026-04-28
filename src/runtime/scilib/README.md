# scilib native backends

This directory contains three C shared-library backends that all export the
symbol set declared in `scilib_shim.h`.  The active backend is selected at
runtime via the `SIMPLE_BLAS_BACKEND` environment variable (default: `mock`).

## Backends

| Library | Env value | Requires | Notes |
|---------|-----------|----------|-------|
| `libspl_scilib_mock.so` | `mock` (default) | nothing | CPU-correct BLAS + LAPACK; safe in interpreter mode (AC-7 / OQ-D) |
| `libspl_scilib_cublas.so` | `cublas` | CUDA 11.7+ | Real cuBLAS_64 BLAS on GPU; ~10-100x faster for large N |
| `libspl_scilib_cusolver.so` | `cusolver` | CUDA 11.7+ | Real cuSOLVER LAPACK (gesv / getrf / getrs) on GPU |

## Build

```sh
# Build mock only (no CUDA required):
make mock

# Build all three (GPU targets auto-skipped if nvcc not found):
make all

# Build GPU backends explicitly (requires nvcc in PATH):
make cublas
make cusolver

# Install to release/<arch>-<os>/lib/:
make install
```

Override `CUDA_HOME` if CUDA is not at the default path:

```sh
make cublas CUDA_HOME=/opt/cuda
```

## Runtime selection

```sh
# Use real cuBLAS for BLAS calls:
SIMPLE_BLAS_BACKEND=cublas bin/simple run myprogram.spl

# Use real cuSOLVER for LAPACK calls:
SIMPLE_BLAS_BACKEND=cusolver bin/simple run myprogram.spl

# Default (mock, safe on any host):
bin/simple run myprogram.spl
```

## Symbol reference

All 16 symbols are forward-declared in `scilib_shim.h`:

- **BLAS (7):** `rt_blas_dgemm`, `rt_blas_dgemv`, `rt_blas_daxpy`,
  `rt_blas_ddot`, `rt_blas_dscal`, `rt_blas_idamax`, `rt_blas_dnrm2`
- **LAPACK (3):** `rt_lapack_dgesv`, `rt_lapack_dgetrf`, `rt_lapack_dgetrs`
- **CUDA memory helpers (4):** `rt_cuda_malloc`, `rt_cuda_free`,
  `rt_cuda_memcpy_htod`, `rt_cuda_memcpy_dtoh`
- **Backend ID (2):** `rt_scilib_backend_name`, `rt_scilib_is_real`

All dimension / stride parameters use `int64_t` for cuBLAS `_64` API parity.
Device pointers from `rt_cuda_malloc` are opaque `int64_t` handles — not
host-deref'able pointers.

## v1 status

Wave 1 (this commit): `scilib_shim.h` + `Makefile` + this README only.

Wave 2 (next): `mock_shim.c`, `cublas_shim.c`, `cusolver_shim.c`.

## Deferred

- OpenBLAS host backend (`openblas_shim.c`) — T-CUDA-03, v1 polish, not blocker.
- Cranelift codegen fast-path for BLAS calls — v2 work.
