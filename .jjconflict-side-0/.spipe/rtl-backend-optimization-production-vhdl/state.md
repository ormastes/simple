# RTL Backend Optimization Production VHDL

## Task Type
feature

## Refined Goal
Build a production-oriented RTL backend optimization path that introduces an explicit HWIR layer, target-aware VHDL hardening, toolchain verification lanes, and QoR/debug evidence for hardware-generated VHDL.

## Acceptance Criteria
1. HWIR foundation exists with typed module, port, signal, register, memory, FSM, pipeline, clock/reset, resource binding, source-map, and cost-model records.
2. Hardware-tagged MIR can be represented as HWIR without changing the existing direct VHDL emission fallback.
3. HWIR legality diagnostics expose stable `HWIR-E-*` codes for unsupported hardware constructs.
4. Existing VHDL backend behavior remains unchanged until the HWIR bridge is explicitly selected.
5. Toolchain validation plans or lanes cover GHDL analysis at minimum and preserve existing VHDL tests.
6. QoR and debuggability follow-on work has concrete artifacts or task boundaries before completion is claimed.

## Phase
implementation

## Source Plan
`doc/03_plan/agent_tasks/rtl_backend_optimization_production_vhdl_agent_plan.md`

## Generated FPGA Replan
`doc/03_plan/agent_tasks/rtl_backend_optimization_production_vhdl_generated_fpga_replan_2026-06-01.md`

## Codex Implementation Evidence - 2026-06-01

- Added RTL CLI dispatch coverage for `simple rtl compare`, `simple rtl qor report`, and `simple rtl explain --map=... --vhdl-line=...`.
- Sanity-checked SimpleOS GUI/network/webserver/database/filesystem coverage while preserving the RTL/VHDL plan scope.
- Fixed the q35 pure-Simple NVMe smoke lane so `--pure-simple` selects the dedicated pure NVMe perf ELF, attaches separate QEMU NVMe namespaces, proves user namespace assignment on data queue 2, and validates the pure marker contract.
- Focused checks passed:
  - `bin/simple test test/01_unit/app/rtl/rtl_command_spec.spl`
  - `bin/simple test test/01_unit/hardware/qor/rtl_qor_spec.spl`
  - `bin/simple test test/01_unit/compiler/backend/vhdl_backend_spec.spl`
  - `bin/simple test test/03_system/compiler/vhdl_backend_cli_smoke_spec.spl`
  - `bin/simple check src/app/rtl src/os/drivers/nvme src/os/services/vfs/q35_pure_nvme_perf_boot.spl`
  - `bin/simple test test/03_system/os_desktop_integration_spec.spl`
  - `bin/simple test test/03_system/database/database_system_spec.spl`
  - `bin/simple test test/03_system/os/network_system_spec.spl`
  - `bin/simple test test/03_system/os/filesystem_system_spec.spl`
  - `bin/simple test test/02_integration/http_baremetal_spec.spl`
  - `sh scripts/os/run_simpleos_q35_smoke.shs --timeout=30`
  - `sh scripts/os/run_simpleos_q35_smoke.shs --pure-simple --timeout=30`
  - `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.

## Generated FPGA Evidence - 2026-06-01

- Replanned the VHDL/FPGA lane around Simple-authored generated RTL rather than direct hand-written VHDL.
- Updated `scripts/check/check-riscv-rtl-linux-smoke.shs` so the public gate runs both `generated_rv32_linux` and `generated_rv64_linux` by default.
- `sh scripts/check/check-riscv-rtl-linux-smoke.shs --timeout=30` passed:
  - RV32 marker: `[GHDL-GEN-RV32] PASS`
  - RV64 marker: `[GHDL-GEN-RV64-LINUX-HANDOFF] PASS`
- KV260 physical gate passed with artifacts in `build/kv260_simple_rv64_linux_check_20260601_084520/`:
  - `PASS artifacts_present`
  - `PASS simple_rv64_elf_header`
  - `PASS kv260_bitstream_loaded`
  - `PASS merged_usb_ps_uart`
  - `PASS generated_rv64_linux_handoff`
  - `INFO network_physical_verification=not_covered`
  - `PASS kv260_simple_rv64_linux_check`
- Remaining boundary: physical FPGA PL UART, network, HTTP, SSH, and Simple DB-backed web route are not yet proven on the softcore.
