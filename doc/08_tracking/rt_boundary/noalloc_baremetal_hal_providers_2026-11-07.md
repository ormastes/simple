# nogc_async_mut_noalloc/baremetal HAL providers (2026-11-07)

Owner: baremetal HAL lane. Reason: the files under
`src/lib/nogc_async_mut_noalloc/baremetal/` (mmio, riscv cmo/csr/sbi/dtb_gen, arm64 sysreg,
x86_64 msr, semihost_transport, syscall, allocator) declare the `rt_*` hardware
intrinsics and expose one-line typed wrappers. They are the typed layer itself: nothing
beneath them in Simple. Product code calls the wrappers, not `rt_*`.
Source: perf-umbrella AC-9 row `src/lib/nogc_async_mut_noalloc` (baseline 358, measured 399,
+41 since 2026-06-15; growth is in these files). Policy: doc/07_guide/os/hal/pure_simple_hal.md.
