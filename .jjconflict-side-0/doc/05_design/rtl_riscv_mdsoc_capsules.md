# RTL RISC-V MDSOC Capsule Architecture

**Feature:** rtl_riscv_mdsoc_reorg
**Date:** 2026-05-02
**Status:** Phase 4 (spec authored; Phase 5 implementation pending)
**Design Phase:** 3-arch decisions D-1 through D-4
**Spec:** doc/06_spec/app/compiler/feature/rtl_mdsoc_capsules_spec.md

---

## Canonical Capsule Names

The Simple-source VHDL emitter is organized into four named MDSOC capsules.
This is an MDSOC-only architecture (compiler/driver class — no ECS layer).

| Capsule Name | Marker | Owner Files | Concern |
|---|---|---|---|
| `vhdl.emit.control` | `# capsule: vhdl.emit.control` | `vhdl_helpers.spl`, `fpga_linux_orchestrator.spl`, `vhdl_ffi.spl`, `adapter_ghdl_rv32.spl`, `riscv_decode.spl` | Decode, sequencing, validation, GHDL invocation |
| `vhdl.emit.data` | `# capsule: vhdl.emit.data` | `vhdl_builder.spl`, `vhdl_memory_templates.spl`, `vhdl_type_mapper.spl`, `fpga_linux_data.spl`, `riscv_fpga_linux_vhdl_templates.spl` | Datapath lowering, register file, ALU, ROM/RAM templates, type mapping |
| `vhdl.emit.state` | `# capsule: vhdl.emit.state` | Process sections of `vhdl_backend.spl` (annotated), sections of `fpga_linux_orchestrator.spl` | CSRs, reservation set, clock-domain sequential state |
| `vhdl.emit.metadata` | `# capsule: vhdl.emit.metadata` | `vhdl_testbench.spl`, `riscv_rtl_debuggability_lint.spl`, `fpga_linux_manifest.spl`, `riscv_generated_core_pkg.spl` | `*.debug.json` sidecar, testbench rendering, source maps, diagnostics |

Re-export facades use marker `# capsule: re-export`.

---

## Plug-In Points

Four named plug-in insertion points for Features A and B.
All are currently empty stubs — no RTL lowering code is present.

| Plug-In Point | Capsule | Stub File | Feature |
|---|---|---|---|
| `vhdl.emit.data.fp` | `vhdl.emit.data` | `vhdl_emit_fp_stub.spl` | Feature A: SIMD/FP RTL lowering |
| `vhdl.emit.data.simd` | `vhdl.emit.data` | `vhdl_emit_simd_stub.spl` | Feature A: SIMD vector datapath |
| `vhdl.emit.state.cache` | `vhdl.emit.state` | `vhdl_emit_cache_stub.spl` | Feature B: L1/L2 cache coherence state |
| `vhdl.emit.state.hart` | `vhdl.emit.state` | `vhdl_emit_hart_stub.spl` | Feature B: multi-hart PC/CSR fan-out |

---

## Physical File Organization

### Phase 5 SA-2: `vhdl_backend.spl` — Annotation Only

Decision D-1: 8 gap-plan agents are actively modifying `vhdl_backend.spl`.
Physical function moves are deferred to Phase 6-refactor. Phase 5 adds
`# capsule: vhdl.emit.X` comment markers per function group. No file splits.

Capsule annotation map (selected key ranges):

| Lines | Block | Capsule |
|---|---|---|
| 1–75 | File header, ABI types (`VhdlPortSpec`, `VhdlReturnAbi`) | `vhdl.emit.data` |
| 76–99 | `create`, `create_resolved`, `empty_span` | `vhdl.emit.control` |
| 119–178 | `compile` (top-level orchestration) | `vhdl.emit.control` |
| 180–196 | `backend_error`, `backend_error_at`, `unsupported_type_error` | `vhdl.emit.metadata` |
| 218–427 | `validate_*`, `validate_module_*`, `validate_function_*` | `vhdl.emit.control` |
| 442–700 | `compile_package_into`, `emit_enum_type_decls`, tuple-type helpers | `vhdl.emit.data` |
| 699–815 | ABI helpers (`vhdl_return_abi`, `vhdl_ports_for_function`) | `vhdl.emit.data` |
| 1396–1445 | `process_operand_to_vhdl`, `local_kind`, `emit_process_dest_assign` | `vhdl.emit.state` |
| 1446–1546 | `compile_function_control_process`, `compile_control_block` | `vhdl.emit.control` |
| 1547–1708 | `compile_process_instruction` | `vhdl.emit.state` |
| 1787–2011 | `compile_instruction` (combinational) | `vhdl.emit.data` |
| 2012–2100 | `compile_terminator`, `compile_if_return_*` | `vhdl.emit.control` |
| 2773–2845 | `backend_kind`, `backend_name`, Codegen trait impl | `vhdl.emit.control` |
| 2844–2885 | `compile_process` | `vhdl.emit.state` |

### Phase 5 SA-3: `riscv_fpga_linux.spl` — Physical 3-File Split

Decision D-2: `riscv_fpga_linux.spl` (4547 lines) is safe to split.

| New File | Lines (budget) | Capsule | Content |
|---|---|---|---|
| `fpga_linux_orchestrator.spl` | < 900 | `vhdl.emit.control` | `RiscvXlen`, `RiscvFpgaLane` identity, `XilinxBoardProfile`, `LinuxArtifactSet`, `FpgaPrepareManifest`, `generate_riscv_fpga_rtl_bundle`, top-level helpers |
| `fpga_linux_data.spl` | < 2700 | `vhdl.emit.data` | `RiscvFpgaLane` VHDL-emission methods: `hardware_source_*`, `package_vhdl`, `core_vhdl_*`, decode definitions |
| `fpga_linux_manifest.spl` | < 200 | `vhdl.emit.metadata` | `debug_sidecar_json`, `debug_sidecar_file_name`, `json_escape`, `json_text_array`, `json_source_map_array`, `json_runner_success_markers`, testbench renderers |
| `riscv_fpga_linux.spl` (facade) | < 30 | `re-export` | Thin `use` + re-export of all three split files |

**Note on data budget:** Phase 3 estimated the data module at ~2855 lines.
The task specification sets the budget at < 2700. Phase 5 SA-3 must either
fit within 2700 lines or record a deviation and file a follow-up split task.

**D-4 invariant:** All `json_*` helper functions live exclusively in
`fpga_linux_manifest.spl`. No other capsule may emit JSON key-value pairs
for the sidecar. This is the AC-3 byte-equal contract.

### Phase 5 SA-4: Plug-In Stub Files

Four new files in `src/compiler/70.backend/backend/vhdl/`:

```
vhdl_emit_fp_stub.spl      — vhdl.emit.data.fp   — Feature A
vhdl_emit_simd_stub.spl    — vhdl.emit.data.simd  — Feature A
vhdl_emit_cache_stub.spl   — vhdl.emit.state.cache — Feature B
vhdl_emit_hart_stub.spl    — vhdl.emit.state.hart  — Feature B
```

`vhdl/__init__.spl` and `vhdl/mod.spl` updated to re-export all 4 stubs.

---

## Dependency Map

```
fpga_linux_data.spl          -> fpga_linux_orchestrator.spl  (RiscvXlen, RiscvFpgaLane structs)
fpga_linux_manifest.spl      -> fpga_linux_orchestrator.spl  (RiscvFpgaLane, GeneratedCoreDebugMetadata)
fpga_linux_orchestrator.spl  -> fpga_linux_data.spl          (RiscvFpgaLane VHDL emission methods)
fpga_linux_orchestrator.spl  -> fpga_linux_manifest.spl      (debug_sidecar_json, debug_sidecar_file_name)
riscv_fpga_linux.spl (facade)-> fpga_linux_orchestrator.spl  (re-export)
riscv_fpga_linux.spl (facade)-> fpga_linux_data.spl          (re-export)
riscv_fpga_linux.spl (facade)-> fpga_linux_manifest.spl      (re-export)

vhdl_emit_fp_stub.spl        -> (none — empty stub)
vhdl_emit_simd_stub.spl      -> (none — empty stub)
vhdl_emit_cache_stub.spl     -> (none — empty stub)
vhdl_emit_hart_stub.spl      -> (none — empty stub)
vhdl/__init__.spl            -> all 4 stubs (re-export)
vhdl/mod.spl                 -> all 4 stubs (re-export)
```

No circular dependencies.

**Cycle watch:** `fpga_linux_manifest.spl` needs `generated_testbench_from_template`
which is data-class. If this creates a cycle at resolution time, move it into
`fpga_linux_manifest.spl` (testbench rendering is Metadata-class). Resolve in Phase 5.

---

## 8-Agent Gap-Plan Capsule Mapping (AC-4)

| Agent | Assignment | Primary Capsule | Secondary |
|---|---|---|---|
| Agent 1 | Typed Hardware Metadata and Return Labels | `vhdl.emit.metadata` | `vhdl.emit.control` |
| Agent 2 | Hardware Call Lowering and Virtual Aggregates | `vhdl.emit.control` | `vhdl.emit.data` |
| Agent 3 | Fixed-Width Bit Semantics for RV32I | `vhdl.emit.data` | `vhdl.emit.control` |
| Agent 4 | Decode and Control Lowering | `vhdl.emit.control` | — |
| Agent 5 | Register File, ROM, and RAM Inference | `vhdl.emit.data` | `vhdl.emit.state` |
| Agent 6 | Clock Domains, Reset, and Sequential State | `vhdl.emit.state` | `vhdl.emit.control` |
| Agent 7 | Composite Ports and Bus Bundles | `vhdl.emit.data` | `vhdl.emit.control` |
| Agent 8 | Simulation, Testbench, and Source Maps | `vhdl.emit.metadata` | `vhdl.emit.control` |

Phase 5 SA-4 adds `<!-- capsule: ... -->` annotation comments to the plan doc
(`doc/03_plan/agent_tasks/pure_simple_vhdl_riscv_gap_spawn_plan.md`).
No task reassignment — labels are advisory only.

---

## Byte-Equal Verification Protocol (AC-2, AC-3)

1. **SA-1 (gate):** Run generation scripts on pre-refactor main; capture sha256
   of all `build/rtl_linux/**/*.vhd` and `*.debug.json` files into
   `doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md`.
2. **SA-2/3/4:** After each commit, re-run scripts and diff sha256 against
   baseline. Any non-empty diff is a hard fail.
3. **If GHDL absent:** Capture sha256 of template `.spl` source files as proxy;
   record absence explicitly in baseline doc.

---

## Sub-Agent Test File Ownership

| Sub-Agent | Test Files Owned (Phase 5) |
|---|---|
| SA-1 | baseline file at `doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md` — no test file |
| SA-2 | `test/system/compiler/rtl_mdsoc_byte_equal_spec.spl` (vhdl_backend annotation side) |
| SA-3 | `test/system/compiler/fpga_linux_split_spec.spl` |
| SA-4 | `test/system/compiler/rtl_mdsoc_capsule_boundary_spec.spl`, `test/system/compiler/rtl_mdsoc_plugin_stubs_spec.spl`, `test/system/compiler/debug_sidecar_json_order_spec.spl` |

---

## Interpreter-Mode Note (AC-8)

All Phase 5 edits are `.spl` source. Verify in interpreter mode
(`bin/simple test`). If compile-mode (`--mode=native`) regressions are
introduced, record as a separate FR and do not mark AC-8 passed until
interpreter-mode passes. See memory: `compile-mode false-greens`.
