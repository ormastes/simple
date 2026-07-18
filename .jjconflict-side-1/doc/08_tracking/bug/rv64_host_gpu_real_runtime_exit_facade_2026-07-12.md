# RV64 host-GPU runtime needs a real QEMU exit facade

The RV64 host-GPU link now selects `freestanding_runtime.c` instead of linking
generated success stubs. Its reachable closure can still require
`rt_qemu_exit_success`, but the real runtime has no architecture-owned exit
facade. Do not restore the generated linker stub or duplicate the SiFive test
MMIO address in the probe.

Resolved for RV64: the architecture leaf now calls `sbi_shutdown()`, using
OpenSBI SRST supplied by the target's existing `-bios default` configuration.

TODO: replace the x86_64 and ARM64 probe leaves' direct runtime exits with
architecture-owned OS exit facades, then remove host-GPU reachability of the
legacy generated stub source entirely.
