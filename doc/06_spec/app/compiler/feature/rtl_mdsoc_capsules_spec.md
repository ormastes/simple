# RTL MDSOC Capsules Specification

**Feature:** rtl_riscv_mdsoc_reorg
**Date:** 2026-05-02
**Status:** Phase 4 — TDD red (specs authored; implementation pending)
**Category:** Infrastructure
**Design:** doc/05_design/rtl_riscv_mdsoc_capsules.md
**State:** .sstack/rtl_riscv_mdsoc_reorg/state.md

---

## 1. Overview

Reorganizes the Simple-source VHDL emitter — the Simple code that produces
VHDL for generated RV32/RV64 Linux RTL lanes — into four named MDSOC capsules
with explicit boundaries. This is MDSOC-only (compiler/driver class; no ECS layer).

The reorganization must not change the generated VHDL bit-for-bit (acceptance
gate: byte-equal sha256 proof). Named plug-in points are created for future
SIMD/FP (Feature A) and SMP/cache (Feature B) RTL hooks.

---

## 2. Acceptance Criteria

| AC | Description | Test File | Status |
|---|---|---|---|
| AC-1 | VHDL emitter split into 4 named MDSOC capsules with `# capsule:` markers | `rtl_mdsoc_capsule_boundary_spec.spl`, `fpga_linux_split_spec.spl` | TDD red |
| AC-2 | Generated VHDL sha256 byte-equal to pre-refactor baseline (RV32 + RV64) | `rtl_mdsoc_byte_equal_spec.spl` | Pending SA-1 |
| AC-3 | `*.debug.json` sidecar `reportMarkers`/`runnerSuccessMarkers` byte-equivalent | `debug_sidecar_json_order_spec.spl`, `rtl_mdsoc_byte_equal_spec.spl` | Pending SA-1 |
| AC-4 | 8-agent plan annotated with capsule mapping; no task reassignment | `rtl_mdsoc_capsule_boundary_spec.spl` (plan annotation tests) | TDD red |
| AC-5 | 4 plug-in stubs: `vhdl.emit.data.fp`, `.simd`, `vhdl.emit.state.cache`, `.hart` | `rtl_mdsoc_plugin_stubs_spec.spl` | TDD red |
| AC-6 | `pure_simple_vhdl_source_of_truth_spec.spl` passes after refactor | `fpga_linux_split_spec.spl` (API preservation) | TDD red |
| AC-7 | `check-riscv-rtl-linux-smoke.shs --rv32-only` and `--rv64-only` PASS | `fpga_linux_split_spec.spl` (smoke precondition) | TDD red |
| AC-8 | Interpreter-mode verification; compile-mode regressions filed separately | All spec files | TDD red |

---

## 3. Capsule Definitions

### `vhdl.emit.control`

**Concern:** Decode, sequencing, entity classification, GHDL invocation,
validation logic, terminator lowering.

**Files:**
- `src/compiler/70.backend/backend/vhdl/vhdl_helpers.spl` (existing)
- `src/hardware/fpga_linux/fpga_linux_orchestrator.spl` (new, Phase 5 SA-3)
- `src/lib/nogc_sync_mut/io/vhdl_ffi.spl` (existing)
- `src/lib/nogc_sync_mut/debug/remote/exec/adapter_ghdl_rv32.spl` (existing)
- `src/hardware/riscv_common/core/riscv_decode.spl` (existing)

**In `vhdl_backend.spl` (annotated, not moved):**
- `create`, `create_resolved`, `compile` (orchestration), `validate_*`
- `compile_function_control_process`, `compile_control_block`
- `compile_terminator`, `compile_if_return_*`
- Codegen trait impl (`backend_kind`, `backend_name`, `compile_module`, etc.)

### `vhdl.emit.data`

**Concern:** Datapath lowering, register file, ALU, ROM/RAM templates, type
mapping, VHDL emission helpers, inline VHDL string templates.

**Files:**
- `src/compiler/70.backend/backend/vhdl/vhdl_builder.spl` (existing)
- `src/compiler/70.backend/backend/vhdl/vhdl_memory_templates.spl` (existing)
- `src/compiler/70.backend/backend/vhdl_type_mapper.spl` (existing)
- `src/hardware/fpga_linux/fpga_linux_data.spl` (new, Phase 5 SA-3)
- `src/hardware/fpga_linux/riscv_fpga_linux_vhdl_templates.spl` (existing)

**Plug-in stubs:**
- `vhdl_emit_fp_stub.spl` (`vhdl.emit.data.fp`) — Feature A
- `vhdl_emit_simd_stub.spl` (`vhdl.emit.data.simd`) — Feature A

### `vhdl.emit.state`

**Concern:** CSRs, reservation set, clock-domain sequential state, clocked
process instruction lowering, process operand handling.

**In `vhdl_backend.spl` (annotated, not moved):**
- `process_operand_to_vhdl`, `local_kind`, `emit_process_dest_assign`
- `compile_process_instruction`, `compile_process_into`, `compile_process`
- `mark_return_chain_handled`, `reset_asserted_literal`

**Plug-in stubs:**
- `vhdl_emit_cache_stub.spl` (`vhdl.emit.state.cache`) — Feature B
- `vhdl_emit_hart_stub.spl` (`vhdl.emit.state.hart`) — Feature B

### `vhdl.emit.metadata`

**Concern:** `*.debug.json` sidecar emission, testbench rendering, source maps,
generated package declarations, diagnostic error emission.

**Files:**
- `src/compiler/70.backend/backend/vhdl/vhdl_testbench.spl` (existing)
- `src/compiler/35.semantics/lint/riscv_rtl_debuggability_lint.spl` (existing)
- `src/hardware/fpga_linux/fpga_linux_manifest.spl` (new, Phase 5 SA-3)
- `src/hardware/riscv_common/pkg/riscv_generated_core_pkg.spl` (existing)

**D-4 invariant:** All `json_*` helpers and `debug_sidecar_json` live
exclusively in `fpga_linux_manifest.spl`. No other file may emit JSON
key-value pairs for the sidecar.

---

## 4. Test Scenarios

### 4.1 `rtl_mdsoc_byte_equal_spec.spl` — AC-2, AC-3

**SA-2 owned. Pending SA-1 baseline.**

| Scenario | `describe` / `it` | AC |
|---|---|---|
| RV32 VHDL sha256 matches baseline | `describe "RTL MDSOC Byte-Equal: AC-2 RV32"` / `it "AC-2: RV32 generated VHDL sha256 matches pre-refactor baseline"` | AC-2 |
| RV64 VHDL sha256 matches baseline | `describe "RTL MDSOC Byte-Equal: AC-2 RV64"` / `it "AC-2: RV64 generated VHDL sha256 matches pre-refactor baseline"` | AC-2 |
| RV32 debug.json sha256 matches baseline | `describe "RTL MDSOC Byte-Equal: AC-3 debug.json"` / `it "AC-3: RV32 .debug.json sha256..."` | AC-3 |
| RV64 debug.json sha256 matches baseline | same describe / `it "AC-3: RV64 .debug.json sha256..."` | AC-3 |
| Missing baseline → pending | `it "AC-2: ... pending until SA-1..."` | AC-2, AC-3 |

**Pending gate:** All byte-comparison `it` blocks emit `pending(...)` when
`doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md` does not exist.

### 4.2 `rtl_mdsoc_capsule_boundary_spec.spl` — AC-1, AC-4, AC-5

**SA-4 owned.**

| Scenario | `describe` / `it` | AC |
|---|---|---|
| Existing emitters have `# capsule:` markers | 9 `it` blocks under "existing emitter files" | AC-1 |
| SA-3 split files have correct markers | 4 `it` blocks under "Phase 5 SA-3 split files" | AC-1 |
| SA-4 stub files have correct markers | 4 `it` blocks under "Phase 5 SA-4 stub files" | AC-5 |
| Plan preamble has `rtl_riscv_mdsoc_reorg` | `it "AC-4: plan preamble mentions rtl_riscv_mdsoc_reorg..."` | AC-4 |
| Plan has capsule annotations for Agents 1, 2, 5 | 3 `it` blocks | AC-4 |

### 4.3 `rtl_mdsoc_plugin_stubs_spec.spl` — AC-5

**SA-4 owned.**

| Scenario | `describe` / `it` | AC |
|---|---|---|
| FP stub exists with correct fn name and TODO | 4 `it` blocks under `vhdl.emit.data.fp` | AC-5 |
| SIMD stub exists with correct fn name and TODO | 4 `it` blocks under `vhdl.emit.data.simd` | AC-5 |
| Cache stub exists with correct fn name and TODO | 4 `it` blocks under `vhdl.emit.state.cache` | AC-5 |
| Hart stub exists with correct fn name and TODO | 4 `it` blocks under `vhdl.emit.state.hart` | AC-5 |
| `__init__.spl` re-exports all 4 stubs | 4 `it` blocks under "re-export facade inclusion" | AC-5 |

### 4.4 `fpga_linux_split_spec.spl` — AC-1, AC-6, AC-7

**SA-3 owned.**

| Scenario | `describe` / `it` | AC |
|---|---|---|
| 3 split files + facade exist | 4 existence `it` blocks | AC-1 |
| Orchestrator < 900 lines | `it "AC-1: fpga_linux_orchestrator.spl is under 900 lines"` | AC-1 |
| Data < 2700 lines (budget conflict flagged) | `it "AC-1: fpga_linux_data.spl is under 2700 lines"` | AC-1 |
| Manifest < 200 lines | `it "AC-1: fpga_linux_manifest.spl is under 200 lines"` | AC-1 |
| Facade re-exports 3 canonical symbols | 3 `it` blocks | AC-1, AC-6 |
| Facade imports 3 capsule files | 3 `it` blocks | AC-1 |
| Smoke script files exist | 2 `it` blocks | AC-7 |
| All 3 capsule files present as smoke precondition | 1 `it` block | AC-7 |

### 4.5 `debug_sidecar_json_order_spec.spl` — AC-3

**SA-4 owned.**

| Scenario | `describe` / `it` | AC |
|---|---|---|
| Manifest source has `reportMarkers` | static grep `it` | AC-3 |
| Manifest source has `runnerSuccessMarkers` | static grep `it` | AC-3 |
| `reportMarkers` precedes `runnerSuccessMarkers` in source | position-comparison `it` | AC-3 |
| `runnerSuccessMarkers` precedes `sourceMap` in source | position-comparison `it` | AC-3 |
| D-4: no `json_` helpers in orchestrator source | static grep `it` | AC-3 |
| RV32 generated debug.json has both keys in order | 3 `it` blocks (pending if no build) | AC-3 |
| RV64 generated debug.json has both keys in order | 2 `it` blocks (pending if no build) | AC-3 |
| Baseline sha256 comparison pending until SA-1 | 1 `pending` `it` | AC-3 |

---

## 5. Budget Conflict Note

Phase 3 architectural sizing estimated `fpga_linux_data.spl` at ~2855 lines.
The Phase 4 task specification sets the budget at < 2700 lines. The task
specification is authoritative. Phase 5 SA-3 must:

1. Fit within 2700 lines, OR
2. Record the overage, file a follow-up split task, and note the deviation
   in the Phase 5 state entry.

The test `fpga_linux_split_spec.spl` enforces < 2700.

---

## 6. Pending Gate Protocol

Tests blocked on SA-1 baseline use `pending("SA-1 baseline gate — ...")` inside
`it` blocks when the runtime check `rt_file_exists(BASELINE_PATH)` returns false.
This matches the `local_ghdl_available()` pattern from
`pure_simple_vhdl_source_of_truth_spec.spl`.

Tests blocked on Phase 5 SA-3/SA-4 file creation use `rt_file_exists(path)` +
`check_msg(exists, "SA-X not run yet — file missing: ...")` to produce
informative failures rather than panics.

---

## 7. Related Documents

- `doc/05_design/rtl_riscv_mdsoc_capsules.md` — canonical capsule reference (this spec links here)
- `doc/03_plan/agent_tasks/pure_simple_vhdl_riscv_gap_spawn_plan.md` — 8-agent plan to annotate
- `doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md` — SA-1 baseline (created in Phase 5)
- `test/system/compiler/pure_simple_vhdl_source_of_truth_spec.spl` — existing spec to keep passing
- `.sstack/rtl_riscv_mdsoc_reorg/state.md` — full phase tracking
