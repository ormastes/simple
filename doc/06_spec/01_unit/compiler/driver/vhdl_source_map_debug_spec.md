# Vhdl Source Map Debug Specification

> Tests covering VHDL source-map HWIR debug metadata.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Source Map Debug Specification

## Scenarios

### VHDL source-map HWIR debug metadata

#### explains a VHDL line through HWIR and Simple source

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- explains a VHDL line through HWIR and Simple source


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explains a VHDL line through HWIR and Simple source")
val result = rtl_explain_vhdl_line_from_map(sample_map(), 8)
check(result.found)
expect result.hwir_id == "port:a:8"
expect result.signal_name == "a"
expect result.source_line == 2
check(result.to_text().contains("width_narrowing"))
```

</details>

#### returns a missing explanation for unmapped lines

- returns a missing explanation for unmapped lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a missing explanation for unmapped lines")
val result = rtl_explain_vhdl_line_from_map(sample_map(), 42)
check(not result.found)
check(result.to_text().contains("no RTL source-map entry"))
```

</details>

#### renders waveform groups from source-map ports

- renders waveform groups from source-map ports


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders waveform groups from source-map ports")
val groups = rtl_waveform_groups_from_map(sample_map())
expect groups.len() == 1
val gtkw = rtl_render_gtkw_from_groups(groups)
check(gtkw.contains("[group] ports"))
check(gtkw.contains("a"))
```

</details>

#### renders first divergence reports

- renders first divergence reports


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders first divergence reports")
val report = rtl_first_divergence_report(12, "0x1000", "0x13", "x1 expected 1 got 0", "", "", "demo.spl:2", "uut.debug_pc", "wave.gtkw")
check(report.contains("First RTL Divergence"))
check(report.contains("uut.debug_pc"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/vhdl_source_map_debug_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering VHDL source-map HWIR debug metadata.
- VHDL source-map HWIR debug metadata

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `60bb32f3ef6a4d0c94823e79e377a035eab9ba070ab53c9d05da77ec089cd860`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `60bb32f3ef6a4d0c94823e79e377a035eab9ba070ab53c9d05da77ec089cd860`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `60bb32f3ef6a4d0c94823e79e377a035eab9ba070ab53c9d05da77ec089cd860`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/vhdl_source_map_debug_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/vhdl_source_map_debug_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/vhdl_source_map_debug_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/vhdl_source_map_debug_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/vhdl_source_map_debug_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'explains a VHDL line through HWIR and Simple source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/vhdl_source_map_debug_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a missing explanation for unmapped lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/vhdl_source_map_debug_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders waveform groups from source-map ports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
