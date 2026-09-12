# RV64 host-GPU runtime needs a real QEMU exit facade
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
