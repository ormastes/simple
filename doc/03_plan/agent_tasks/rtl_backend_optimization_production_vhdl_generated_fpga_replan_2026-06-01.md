# RTL Backend Optimization Production VHDL - Generated FPGA Replan

Date: 2026-06-01

## Scope Reset

The production VHDL plan is now centered on the Simple-authored RISC-V RTL path:

1. Simple hardware source is the authoritative RTL input.
2. Generated VHDL is an artifact of the Simple pipeline, not the source of truth.
3. RV32 and RV64 generated lanes must remain symmetric at the public smoke-command layer.
4. Physical FPGA evidence must be separated from GHDL/QEMU evidence.
5. SimpleOS web, network, database, and filesystem claims must name the target where they were proven.

## Current Evidence

### Generated From Simple

The generated bundle and sidecar tests prove these markers:

- `authoritative_rtl_provenance = "simple-compiler-generated"`
- `pure_simple_authoritative_rtl = "true"`
- RV32 proof lane: `generated_rv32_linux`
- RV64 proof lane: `generated_rv64_linux`

Verified commands:

```bash
bin/simple test test/unit/hardware/fpga_linux/riscv_fpga_linux_spec.spl
bin/simple test test/system/app/hardware/feature/riscv_fpga_linux_spec.spl
bin/simple test test/system/app/hardware/feature/rv64_linux_rtl_pipeline_spec.spl
bin/simple test test/unit/compiler/lint/riscv_rtl_debuggability_spec.spl
sh scripts/check-riscv-rtl-linux-smoke.shs --timeout=30
```

`scripts/check-riscv-rtl-linux-smoke.shs` now runs both public lanes by default and supports `--rv32-only` and `--rv64-only`.

### Physical FPGA

KV260 physical check run on 2026-06-01:

```bash
CAPTURE_SECONDS=10 LINUX_TIMEOUT=30 sh scripts/fpga/check_kv260_simple_rv64_linux.shs
```

Result:

- `PASS artifacts_present`
- `PASS simple_rv64_elf_header`
- `PASS kv260_bitstream_loaded`
- `INFO pl_uart_on_merged_usb=no_output rc=1`
- `PASS merged_usb_ps_uart`
- `PASS generated_rv64_linux_handoff`
- `INFO network_physical_verification=not_covered`
- `PASS kv260_simple_rv64_linux_check`

Artifact directory:

```text
build/kv260_simple_rv64_linux_check_20260601_084520
```

This proves bitstream programming and board sanity for the current KV260 RV64 flow. It does not prove physical PL UART boot output, physical SimpleOS network readiness, HTTP response, SSH, or Simple DB service behavior on the FPGA softcore.

### SimpleOS Non-FPGA Evidence

The current verified SimpleOS service evidence is target-specific:

- x86_64 q35 normal smoke: NVMe read/write restore and VirtIO-net TX/RX.
- x86_64 q35 pure Simple NVMe performance lane: user namespace assignment, FAT32/NVFS/DBFS shared direct I/O, and `nvme_perf reason=ready`.
- RISC-V QEMU boot specs: RV32 and RV64 boot specs pass, but these are QEMU CPU lanes, not generated-RTL FPGA lanes.
- RV64 QEMU HTTP smoke with storage passes the HTTP-only gate; TLS is explicitly skipped.
- Host/interpreter Simple DB and web hot-path benchmarks pass separately.

## Remaining Work

### Phase A - Generated RTL Contract

- Keep RV32/RV64 generated smoke wrapper symmetric.
- Keep sidecar provenance checks release-blocking for generated bundles.
- Add a CI summary artifact that records generated RV32/RV64 pass markers in one file.

### Phase B - FPGA Physical Runtime

- Capture PL UART from the PMOD `H12/E10` path or route PL UART to a merged USB channel.
- Add a nonzero-exit FPGA runtime gate that requires:
  - bitstream startup high,
  - PL UART SimpleOS boot marker,
  - target network readiness marker,
  - HTTP `/health` and `/` transcripts from the physical target,
  - optional SSH banner/login transcript when sshd is enabled.
- Do not use QEMU HTTP or GHDL output as physical FPGA network proof.

### Phase C - SimpleOS Web + DB on FPGA

- Define a physical FPGA service scenario that starts SimpleOS web server with a Simple DB-backed endpoint.
- Required endpoint evidence:
  - `GET /health` returns 200,
  - a DB-backed route returns deterministic data,
  - response log includes latency and request count,
  - failure is nonzero for timeout, stale DB response, or missing target transport.
- Until this exists, web server and Simple DB are only separately verified on non-FPGA lanes.

### Phase D - Documentation and Release Gates

- Update `doc/07_guide/hardware/simple_generated_fpga_rtl.md` whenever generated lane semantics change.
- Update `doc/07_guide/hardware/kv260_rv64gc_fpga_boot.md` after each physical KV260 run.
- Keep `.spipe/rtl-backend-optimization-production-vhdl/state.md` evidence current.
- Before release/push, rerun:

```bash
bin/simple test test/unit/hardware/fpga_linux/check_riscv_rtl_linux_smoke_spec.spl
bin/simple test test/unit/hardware/fpga_linux/riscv_fpga_linux_spec.spl
bin/simple test test/system/app/hardware/feature/riscv_fpga_linux_spec.spl
bin/simple test test/system/app/hardware/feature/rv64_linux_rtl_pipeline_spec.spl
bin/simple test test/unit/compiler/lint/riscv_rtl_debuggability_spec.spl
sh scripts/check-riscv-rtl-linux-smoke.shs --timeout=30
sh scripts/fpga/check_kv260_simple_rv64_linux.shs
find doc/06_spec -name '*_spec.spl' | wc -l
```

