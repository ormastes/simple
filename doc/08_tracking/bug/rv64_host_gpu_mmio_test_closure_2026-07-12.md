# RV64 host-GPU MMIO test closure

The canonical RV64 host-GPU entry closure reaches the correct PCI, ivshmem,
protocol, MMIO, and SBI owners. `os.kernel.boot.mmio` also contains allocating
test-region classes and arrays, so its production closure emits array/runtime
support that should not be required by the baremetal probe.

The real RV freestanding runtime already owns the observed `rt_*` support;
adding firmware-local shims is forbidden. A remaining bare `unsafe` reference
would instead belong to LLVM inline-assembly lowering for the SBI shutdown
path.

The production/test MMIO boundary is now split. A canonical RV64 link no longer
reports the dynamic test arrays; it reaches the freestanding-runtime selection
and SBI lowering boundary instead. Stage 2 reports unresolved
`rt_for_iterable`, `rt_pool_safepoint`, `rt_memory_barrier`, and bare `unsafe`,
even though the first three exist in the RV freestanding runtime source. The
raw MMIO split also removed the unused `rt_invlpg` closure dependency. Stage 3
exits without producing an ELF.

TODO: fix deployed RV freestanding-runtime object selection and lower SBI
`unsafe`/inline assembly at the compiler owner. Do not add firmware-local
runtime shims.
