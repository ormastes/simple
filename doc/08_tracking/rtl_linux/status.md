# RISC-V Local RTL Linux Status

Current target: repo-native generated RTL evidence for both RV32 and RV64 Linux lanes. External LiteX/CVA6 reference lanes are not the active acceptance path for this tracker.

## Lanes

| Lane | Backend | Runner | Current PASS Meaning |
|------|---------|--------|----------------------|
| RV32 | `generated-rv32-ghdl` | `scripts/rtl_riscv32_linux_generated.shs` | PASS means the authoritative generated RV32 Linux lane passed its bounded generated proof gates and then ran the repo-native generated payload acceptance lane under the emitted `rv32/rtl` bundle root. |
| RV64 | `generated-rv64-ghdl` | `scripts/rtl_riscv64_linux_generated.shs` | PASS means the authoritative generated RV64 Linux lane passed its bounded proof gates and then ran the repo-native generated Linux payload lane under the emitted `rv64/rtl` bundle root. |

## Boundaries

- QEMU RISC-V boot scripts remain functional references, not RTL success evidence.
- External LiteX/VexRiscv and CVA6 Verilator lanes remain useful cross-checks, but they do not satisfy generated-only acceptance.
- Generated RV32 and RV64 GHDL PASS remains a generated-lane acceptance gate, not a substitute for board-level UART confirmation on `mlk_s02_100t`.
- The current repo-native RV64 script no longer uses external `bbl`; it builds and runs the local `ghdl_boot_info_entry` payload instead.
- Generated lanes now emit `*.debug.json` sidecars beside the VHDL/source bundle; those sidecars are the canonical machine-readable debug contract for lint/static-analysis, while the existing VHDL/source-map comments remain the human-readable review surface.
- In that sidecar, `reportMarkers` are failure/debug-context telemetry for trap edges, halt edges, heartbeats, progress reports, and similar forensic context.
- In that sidecar, `runnerSuccessMarkers` are the canonical machine-readable summary of top-level runner PASS markers for each generated acceptance testbench.
- Board-level synth/program/UART orchestration for `MLK-S02-100T` now lives at `scripts/mlk_s02_100t_generated_linux.shs`, with per-arch output contracts emitted in `board_linux_boot_products.sdn`.
- Generated bundle manifests and debug sidecars now publish explicit provenance fields separating the authoritative `simple-compiler-generated` RTL root from transitional emitted VHDL wrapper/testbench artifacts.
- RV32 now uses a compiled generated payload lane that must emit the Linux UART acceptance markers and preserve `a0`, `a1`, DTB validity, and `satp = 0`.

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
