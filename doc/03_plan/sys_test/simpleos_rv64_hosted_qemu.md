<!-- codex-impl -->
# SimpleOS RV64 Hosted QEMU System Test Plan

1. Run `bin/simple test test/unit/os/qemu_runner_spec.spl` and confirm the new `riscv64-hosted` scenario is registered with disk and host-forwarded networking.
2. Run `sh scripts/qemu_riscv64.shs --smoke --skip-build` and confirm the smoke lane now auto-attaches its RV64 disk image instead of failing immediately on missing media.
3. Run `sh scripts/qemu_riscv64.shs --hosted --skip-build` and confirm the lane emits hosted preflight markers, then fails on SSH/HTTP probes until guest services are implemented.
