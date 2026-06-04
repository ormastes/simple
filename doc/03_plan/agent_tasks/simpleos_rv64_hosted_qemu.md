<!-- codex-impl -->
# SimpleOS RV64 Hosted QEMU Agent Tasks

- Task 1: Add truthful RV64 hosted scenario and target registration in `src/os/qemu_runner.spl`.
- Task 2: Add a dedicated RV64 hosted preflight guest entry that keeps QEMU alive for host probes.
- Task 3: Extend `scripts/qemu_riscv64.shs` with `--hosted`, active SSH/HTTP probes, and auto-attached smoke media.
- Task 4: Update RV64 smoke docs and entries so the existing SMF lane is explicitly smoke-only.
