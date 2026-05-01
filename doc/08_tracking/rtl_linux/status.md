# RISC-V Local RTL Linux Status

Current target: repo-native generated RTL evidence for both RV32 and RV64 Linux lanes. External LiteX/CVA6 reference lanes are not the active acceptance path for this tracker.

## Lanes

| Lane | Backend | Runner | Current PASS Meaning |
|------|---------|--------|----------------------|
| RV32 | `generated-rv32-ghdl` | `scripts/rtl_riscv32_linux_generated.shs` | PASS means the authoritative generated RV32 Linux handoff and real-DTB acceptance gates both pass locally. |
| RV64 | `generated-rv64-ghdl` | `scripts/rtl_riscv64_linux_generated.shs` | PASS means the authoritative generated RV64 FW_JUMP / real-DTB / Sv39 acceptance gates and the repo-native compiled-payload boot-info DTB proof all pass locally. |

## Boundaries

- QEMU RISC-V boot scripts remain functional references, not RTL success evidence.
- External LiteX/VexRiscv and CVA6 Verilator lanes remain useful cross-checks, but they do not satisfy generated-only acceptance.
- Generated RV32 and RV64 GHDL PASS does not yet equal full Linux/userspace boot PASS for repo-native generated RTL.
- The current repo-native RV64 script no longer uses external `bbl`; it builds and runs the local `ghdl_boot_info_entry` payload instead.
- Generated lanes now emit `*.debug.json` sidecars beside the VHDL/source bundle; those sidecars are the canonical machine-readable debug contract for lint/static-analysis, while the existing VHDL/source-map comments remain the human-readable review surface.
- Board-level synth/program/UART orchestration for `MLK-S02-100T` now lives at `scripts/mlk_s02_100t_generated_linux.shs`, with per-arch output contracts emitted in `board_linux_boot_products.sdn`.

## Commands

Tool probe:

```sh
sh scripts/check-riscv-rtl-linux-smoke.shs --check-tools
```

Run both generated lanes:

```sh
sh scripts/check-riscv-rtl-linux-smoke.shs
```

Run one lane:

```sh
sh scripts/check-riscv-rtl-linux-smoke.shs --rv32-only
sh scripts/check-riscv-rtl-linux-smoke.shs --rv64-only
```
