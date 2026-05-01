<!-- codex-impl -->
# SimpleOS RV64 Hosted QEMU Design

- Add `scenario_riscv64_hosted()` and `get_riscv64_hosted_target()` in [src/os/qemu_runner.spl](/home/ormastes/dev/pub/simple/src/os/qemu_runner.spl:1330) so scenario lookup, timeout selection, and disk materialization know about the lane.
- Add [examples/simple_os/arch/riscv64/hosted_entry.spl](/home/ormastes/dev/pub/simple/examples/simple_os/arch/riscv64/hosted_entry.spl:1) as a dedicated preflight guest. It initializes POSIX, enables the existing RV64 network path, requires disk readability, prints explicit preflight markers, then stays alive for host probes.
- Extend [scripts/qemu_riscv64.shs](/home/ormastes/dev/pub/simple/scripts/qemu_riscv64.shs:1) with `--hosted`, host-side TCP/SSH/HTTP probes, and automatic disk creation for RV64 smoke/shared-service lanes.
- Remove the fake desktop process-backed marker from the RV64 smoke entries so smoke success no longer masquerades as hosted proof.
