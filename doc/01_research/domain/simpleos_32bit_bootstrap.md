# SimpleOS 32-bit bootstrap — domain research

Cross-bootstrap proof combines three independent concerns: architecture ABI,
artifact lineage, and execution on the intended machine model. A successful
host compilation alone does not establish target execution or self-host
convergence.

QEMU documents distinct system targets for i386, Arm, and RISC-V, including a
32-bit RISC-V `virt` invocation. Consequently each SimpleOS row must bind its
receipt to the exact emulator and machine profile rather than treating a
generic QEMU exit as portable evidence. QEMU also warns that semihosting can
expose the host filesystem, so the acceptance lane uses guest filesystem
execution markers instead of semihosting as proof.

The practical evidence model is reproducible-build style provenance: hash both
phases, bind Phase 2 to Phase 1, hash linker/sysroot/tool inputs, forbid stub
fallback, and add a fresh nonce to prevent replaying serial logs. Architecture
specific ABI and linker values remain profile data, not operator choices.

References:

- [QEMU system emulator targets](https://www.qemu.org/docs/master/system/targets.html)
- [QEMU system emulation](https://www.qemu.org/docs/master/system/index.html)
- [QEMU RISC-V virt platform](https://www.qemu.org/docs/master/system/riscv/virt.html)
- [QEMU invocation and semihosting warning](https://www.qemu.org/docs/master/system/qemu-manpage.html)

