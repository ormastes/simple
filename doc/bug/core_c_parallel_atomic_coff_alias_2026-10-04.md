# Core-C CPU atomics lose their COFF section owner

Both Windows LLVM and Cranelift Phase2 candidates compiled all 1180 modules,
then failed linking six `rt_par_atomic_*_i64` references from the Rust runtime
extern registry. lld reported relocations against symbols in discarded sections.

The frozen `simple_native_all.lib` contains CPU and GPU names at the same
offset in six COMDAT sections: add, subtract, exchange, compare-exchange,
minimum, and maximum. Core-C supplies strong GPU trap definitions. Replacing
the GPU COMDAT leader also discards its CPU alias, although the registry still
references that alias. This is a provider ownership failure, not a missing
implementation in the Rust source.

## Repair

Give each CPU entry a strong implementation in the core-C provider. The ABI
continues to accept a valid, aligned pointer to i64 storage. All operations are
sequentially consistent and return the previous value. Compare-exchange returns
the observed value on failure. Signed minimum and maximum perform a CAS RMW
even when the stored value is unchanged, preserving the Rust atomic contract.
Add and subtract use atomic fetch operations with wrapping arithmetic.

## Regression

`test/01_unit/runtime/core_parallel_atomics_test.c` checks all six operations,
both compare-exchange paths, changed and unchanged min/max, signed extremes,
wrapping arithmetic, and 160000 increments from eight threads. It also checks
the sum of previous values returned under contention. Compile this fixture
against the core-C provider using the normal native runtime link libraries;
on POSIX, include pthread support.

The integration regression is the actual Windows compiler link using the
preserved 1180 module objects, original Rust archive and rebuilt core-C
provider. A projected Rust object did not retain the registry relocation edge
reliably and is not accepted as integration evidence. Existing duplicate-symbol
link policy is unchanged; CPU entries must resolve to the real implementation,
never the GPU traps.
