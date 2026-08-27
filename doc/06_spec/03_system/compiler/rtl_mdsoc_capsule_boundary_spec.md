# RTL MDSOC Capsule Boundary Specification

> Verifies that every VHDL emitter `.spl` file carries a `# capsule:` marker line near the top, and that no cross-capsule mutable state exists in the emitter modules.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RTL MDSOC Capsule Boundary Specification

Verifies that every VHDL emitter `.spl` file carries a `# capsule:` marker line near the top, and that no cross-capsule mutable state exists in the emitter modules.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #rtl-mdsoc-reorg |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | doc/02_requirements/feature/rtl_riscv_mdsoc_reorg.md |
| Design | doc/05_design/rtl_riscv_mdsoc_capsules.md |
| Source | `test/03_system/compiler/rtl_mdsoc_capsule_boundary_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that every VHDL emitter `.spl` file carries a `# capsule:` marker
line near the top, and that no cross-capsule mutable state exists in the
emitter modules.

## Capsule Marker Contract

Every emitter `.spl` file MUST contain a `# capsule: vhdl.emit.<name>` line
near the top (within the first 40 lines). Re-export facade files
(`mod.spl`, `__init__.spl`) use `# capsule: re-export`.

The 14 emitter files (from Phase 2 research):
1.  src/compiler/70.backend/backend/vhdl_backend.spl
2.  src/compiler/70.backend/backend/vhdl/vhdl_builder.spl
3.  src/compiler/70.backend/backend/vhdl/vhdl_helpers.spl
4.  src/compiler/70.backend/backend/vhdl/vhdl_memory_templates.spl
5.  src/compiler/70.backend/backend/vhdl/vhdl_testbench.spl
6.  src/compiler/70.backend/backend/vhdl/mod.spl
7.  src/compiler/70.backend/backend/vhdl/__init__.spl
8.  src/compiler/70.backend/backend/vhdl_type_mapper.spl
9.  src/compiler/35.semantics/lint/riscv_rtl_debuggability_lint.spl
10. src/hardware/fpga_linux/fpga_linux_orchestrator.spl   (new — Phase 5 SA-3)
11. src/hardware/fpga_linux/fpga_linux_data.spl           (new — Phase 5 SA-3)
12. src/hardware/fpga_linux/fpga_linux_manifest.spl       (new — Phase 5 SA-3)
13. src/hardware/fpga_linux/riscv_fpga_linux.spl          (re-export facade — Phase 5 SA-3)
14. src/compiler/70.backend/backend/vhdl/vhdl_emit_fp_stub.spl    (new — Phase 5 SA-4)

## Acceptance Criteria

- AC-1: MDSOC capsule boundaries are explicit and marked in source
- AC-4: 8-agent plan annotations include Capsule: markers
- AC-5: Plug-in points for SIMD/FP and SMP/cache are present

## Scenarios

### RTL MDSOC Capsule Markers: existing emitter files (AC-1)

#### AC-1: vhdl_backend.spl has a capsule marker

- AC-1: vhdl_backend.spl has a capsule marker
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: vhdl_backend.spl has a capsule marker")
val path = vhdl_backend_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val has_marker = has_capsule_marker(path)
expect(has_marker).to_equal(true)
```

</details>

#### AC-1: vhdl_builder.spl has capsule marker vhdl.emit.data

- AC-1: vhdl_builder.spl has capsule marker vhdl.emit.data
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: vhdl_builder.spl has capsule marker vhdl.emit.data")
val path = vhdl_builder_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val has_marker = has_capsule_marker_value(path, "vhdl.emit.data")
expect(has_marker).to_equal(true)
```

</details>

#### AC-1: vhdl_helpers.spl has capsule marker vhdl.emit.control

- AC-1: vhdl_helpers.spl has capsule marker vhdl.emit.control
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: vhdl_helpers.spl has capsule marker vhdl.emit.control")
val path = vhdl_helpers_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val has_marker = has_capsule_marker_value(path, "vhdl.emit.control")
expect(has_marker).to_equal(true)
```

</details>

#### AC-1: vhdl_memory_templates.spl has capsule marker vhdl.emit.data

- AC-1: vhdl_memory_templates.spl has capsule marker vhdl.emit.data
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: vhdl_memory_templates.spl has capsule marker vhdl.emit.data")
val path = vhdl_mem_templates_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val has_marker = has_capsule_marker_value(path, "vhdl.emit.data")
expect(has_marker).to_equal(true)
```

</details>

#### AC-1: vhdl_testbench.spl has capsule marker vhdl.emit.metadata

- AC-1: vhdl_testbench.spl has capsule marker vhdl.emit.metadata
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: vhdl_testbench.spl has capsule marker vhdl.emit.metadata")
val path = vhdl_testbench_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val has_marker = has_capsule_marker_value(path, "vhdl.emit.metadata")
expect(has_marker).to_equal(true)
```

</details>

#### AC-1: vhdl/mod.spl has capsule marker re-export

- AC-1: vhdl/mod.spl has capsule marker re-export
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: vhdl/mod.spl has capsule marker re-export")
val path = vhdl_mod_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val has_marker = has_capsule_marker_value(path, "re-export")
expect(has_marker).to_equal(true)
```

</details>

#### AC-1: vhdl/__init__.spl has capsule marker re-export

- AC-1: vhdl/__init__.spl has capsule marker re-export
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: vhdl/__init__.spl has capsule marker re-export")
val path = vhdl_init_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val has_marker = has_capsule_marker_value(path, "re-export")
expect(has_marker).to_equal(true)
```

</details>

#### AC-1: vhdl_type_mapper.spl has capsule marker vhdl.emit.data

- AC-1: vhdl_type_mapper.spl has capsule marker vhdl.emit.data
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: vhdl_type_mapper.spl has capsule marker vhdl.emit.data")
val path = vhdl_type_mapper_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val has_marker = has_capsule_marker_value(path, "vhdl.emit.data")
expect(has_marker).to_equal(true)
```

</details>

#### AC-1: riscv_rtl_debuggability_lint.spl has capsule marker vhdl.emit.metadata

- AC-1: riscv_rtl_debuggability_lint.spl has capsule marker vhdl.emit.metadata
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: riscv_rtl_debuggability_lint.spl has capsule marker vhdl.emit.metadata")
val path = rtl_debug_lint_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val has_marker = has_capsule_marker_value(path, "vhdl.emit.metadata")
expect(has_marker).to_equal(true)
```

</details>

### RTL MDSOC Capsule Markers: Phase 5 SA-3 split files (AC-1)

#### AC-1: fpga_linux_orchestrator.spl exists with capsule marker vhdl.emit.control

- AC-1: fpga_linux_orchestrator.spl exists with capsule marker vhdl.emit.control
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: fpga_linux_orchestrator.spl exists with capsule marker vhdl.emit.control")
val path = fpga_orch_path()
check_msg(rt_file_exists(path), "file not found (SA-3 not run yet): " + path)
val has_marker = has_capsule_marker_value(path, "vhdl.emit.control")
expect(has_marker).to_equal(true)
```

</details>

#### AC-1: fpga_linux_data.spl exists with capsule marker vhdl.emit.data

- AC-1: fpga_linux_data.spl exists with capsule marker vhdl.emit.data
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: fpga_linux_data.spl exists with capsule marker vhdl.emit.data")
val path = fpga_data_path()
check_msg(rt_file_exists(path), "file not found (SA-3 not run yet): " + path)
val has_marker = has_capsule_marker_value(path, "vhdl.emit.data")
expect(has_marker).to_equal(true)
```

</details>

#### AC-1: fpga_linux_manifest.spl exists with capsule marker vhdl.emit.metadata

- AC-1: fpga_linux_manifest.spl exists with capsule marker vhdl.emit.metadata
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: fpga_linux_manifest.spl exists with capsule marker vhdl.emit.metadata")
val path = fpga_manifest_path()
check_msg(rt_file_exists(path), "file not found (SA-3 not run yet): " + path)
val has_marker = has_capsule_marker_value(path, "vhdl.emit.metadata")
expect(has_marker).to_equal(true)
```

</details>

#### AC-1: riscv_fpga_linux.spl re-export facade has capsule marker re-export

- AC-1: riscv_fpga_linux.spl re-export facade has capsule marker re-export
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: riscv_fpga_linux.spl re-export facade has capsule marker re-export")
val path = fpga_facade_path()
check_msg(rt_file_exists(path), "file not found: " + path)
val has_marker = has_capsule_marker_value(path, "re-export")
expect(has_marker).to_equal(true)
```

</details>

### RTL MDSOC Capsule Markers: Phase 5 SA-4 stub files (AC-5)

#### AC-5: vhdl_emit_fp_stub.spl exists with capsule marker vhdl.emit.data.fp

- AC-5: vhdl_emit_fp_stub.spl exists with capsule marker vhdl.emit.data.fp
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_fp_stub.spl exists with capsule marker vhdl.emit.data.fp")
val path = stub_fp_path()
check_msg(rt_file_exists(path), "file not found (SA-4 not run yet): " + path)
val has_marker = has_capsule_marker_value(path, "vhdl.emit.data.fp")
expect(has_marker).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_simd_stub.spl exists with capsule marker vhdl.emit.data.simd

- AC-5: vhdl_emit_simd_stub.spl exists with capsule marker vhdl.emit.data.simd
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_simd_stub.spl exists with capsule marker vhdl.emit.data.simd")
val path = stub_simd_path()
check_msg(rt_file_exists(path), "file not found (SA-4 not run yet): " + path)
val has_marker = has_capsule_marker_value(path, "vhdl.emit.data.simd")
expect(has_marker).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_cache_stub.spl exists with capsule marker vhdl.emit.state.cache

- AC-5: vhdl_emit_cache_stub.spl exists with capsule marker vhdl.emit.state.cache
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_cache_stub.spl exists with capsule marker vhdl.emit.state.cache")
val path = stub_cache_path()
check_msg(rt_file_exists(path), "file not found (SA-4 not run yet): " + path)
val has_marker = has_capsule_marker_value(path, "vhdl.emit.state.cache")
expect(has_marker).to_equal(true)
```

</details>

#### AC-5: vhdl_emit_hart_stub.spl exists with capsule marker vhdl.emit.state.hart

- AC-5: vhdl_emit_hart_stub.spl exists with capsule marker vhdl.emit.state.hart
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: vhdl_emit_hart_stub.spl exists with capsule marker vhdl.emit.state.hart")
val path = stub_hart_path()
check_msg(rt_file_exists(path), "file not found (SA-4 not run yet): " + path)
val has_marker = has_capsule_marker_value(path, "vhdl.emit.state.hart")
expect(has_marker).to_equal(true)
```

</details>

### RTL MDSOC 8-Agent Plan Capsule Annotations (AC-4)

#### AC-4: plan file exists

- AC-4: plan file exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-4: plan file exists")
val path = plan_path()
val exists = rt_file_exists(path)
expect(exists).to_equal(true)
```

</details>

#### AC-4: plan preamble mentions rtl_riscv_mdsoc_reorg capsule mapping

- AC-4: plan preamble mentions rtl_riscv_mdsoc_reorg capsule mapping
   - Expected: has_preamble is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-4: plan preamble mentions rtl_riscv_mdsoc_reorg capsule mapping")
val path = plan_path()
check_msg(rt_file_exists(path), "plan file not found: " + path)
val content = read_file(path)
val has_preamble = content.contains("rtl_riscv_mdsoc_reorg")
expect(has_preamble).to_equal(true)
```

</details>

#### AC-4: Agent 1 section has Capsule annotation for vhdl.emit.metadata

- AC-4: Agent 1 section has Capsule annotation for vhdl.emit.metadata
   - Expected: has_annotation is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-4: Agent 1 section has Capsule annotation for vhdl.emit.metadata")
val path = plan_path()
check_msg(rt_file_exists(path), "plan file not found: " + path)
val content = read_file(path)
val has_annotation = content.contains("capsule: vhdl.emit.metadata")
expect(has_annotation).to_equal(true)
```

</details>

#### AC-4: Agent 2 section has Capsule annotation for vhdl.emit.control

- AC-4: Agent 2 section has Capsule annotation for vhdl.emit.control
   - Expected: has_annotation is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-4: Agent 2 section has Capsule annotation for vhdl.emit.control")
val path = plan_path()
check_msg(rt_file_exists(path), "plan file not found: " + path)
val content = read_file(path)
val has_annotation = content.contains("capsule: vhdl.emit.control")
expect(has_annotation).to_equal(true)
```

</details>

#### AC-4: Agent 5 section has Capsule annotation for vhdl.emit.state

- AC-4: Agent 5 section has Capsule annotation for vhdl.emit.state
   - Expected: has_annotation is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-4: Agent 5 section has Capsule annotation for vhdl.emit.state")
val path = plan_path()
check_msg(rt_file_exists(path), "plan file not found: " + path)
val content = read_file(path)
val has_annotation = content.contains("capsule: vhdl.emit.state")
expect(has_annotation).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/rtl_riscv_mdsoc_reorg.md`
- **Design:** `doc/05_design/rtl_riscv_mdsoc_capsules.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b4f12ce8c3a3b4b5aa8e51be0a1f0293f181c2116ffe6d114176b32b685fe2a9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b4f12ce8c3a3b4b5aa8e51be0a1f0293f181c2116ffe6d114176b32b685fe2a9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b4f12ce8c3a3b4b5aa8e51be0a1f0293f181c2116ffe6d114176b32b685fe2a9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/rtl_mdsoc_capsule_boundary_spec.spl
mirror: doc/06_spec/03_system/compiler/rtl_mdsoc_capsule_boundary_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/rtl_mdsoc_capsule_boundary_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/rtl_mdsoc_capsule_boundary_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/rtl_mdsoc_capsule_boundary_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: vhdl_backend.spl has a capsule marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/rtl_mdsoc_capsule_boundary_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: vhdl_builder.spl has capsule marker vhdl.emit.data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/rtl_mdsoc_capsule_boundary_spec.spl:160:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: vhdl_helpers.spl has capsule marker vhdl.emit.control' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
