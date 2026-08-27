# SimpleOS C++ aligned-new false success

## Status

Mitigated: unsupported alignment aborts in the no-exceptions C++ ABI.

## Defect

The C++17 scalar aligned-new ABI symbol ignored its `align_val_t` argument and
delegated directly to ordinary `malloc`. The SimpleOS allocator only proves
16-byte payload alignment, so `new alignas(64) T` could receive misaligned
storage and immediately invoke C++ undefined behavior.

## Current boundary

Scalar and array aligned-new accept a nonzero power-of-two alignment no larger
than `SIMPLEOS_MALLOC_ALIGNMENT` (16). Larger or malformed requests abort;
they never return a false-success pointer. Nothrow new also promotes zero-size
requests to one byte.

All scalar/array, sized/unsized aligned-delete ABI symbols free the same owned
allocation. Aligned-nothrow new returns `NULL` for unsupported alignment or
allocation failure, as required by its no-throw contract.

## Evidence

`test/01_unit/os/libc/simpleos_cxxabi_aligned_new_safety_test.c` passed under
strict C compilation. It verifies valid 16-byte scalar/array allocation and
that a 64-byte throwing request terminates in a child process rather than
returning. It also covers every aligned-delete shape and nothrow success/fail
semantics.

A host `clang++ -std=c++17 -fno-exceptions -fno-rtti -fsized-deallocation`
smoke confirms an `alignas(64)` object emits `_ZnwmSt11align_val_t` and
`_ZdlPvmSt11align_val_t`, the throwing ABI boundary above. This is symbol-shape
evidence, not SimpleOS target execution.

## Follow-up

Supporting larger C++ alignment requires the same allocator-owned
aligned-block representation needed by `posix_memalign`; do not widen either
surface independently.
