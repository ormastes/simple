# Host Gpu Lane Codegen Marker Specification

> Tests covering Host/GPU lane native codegen markers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Gpu Lane Codegen Marker Specification

## Scenarios

### Host/GPU lane native codegen markers

#### consumes lane markers as queue-boundary accounting instead of unsupported instructions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- consumes lane markers as queue-boundary accounting instead of unsupported instructions
   - Expected: marker_codegen_score() equals `1111111`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("consumes lane markers as queue-boundary accounting instead of unsupported instructions")
expect(marker_codegen_score()).to_equal(1111111)
```

</details>

#### diagnoses an unmatched host GPU lane end marker

- diagnoses an unmatched host GPU lane end marker
   - Expected: unmatched_end_error_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("diagnoses an unmatched host GPU lane end marker")
expect(unmatched_end_error_count()).to_equal(1)
```

</details>

#### keeps Cranelift helper calls uniquely named for bootstrap dispatch

- keeps Cranelift helper calls uniquely named for bootstrap dispatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps Cranelift helper calls uniquely named for bootstrap dispatch")
val source = legacy_codegen_source()

expect(source).to_contain("self.compile_cranelift_terminator(block.terminator)")
expect(source).to_contain("val cl_value = self.compile_cranelift_const(value, type_)")
expect(source).to_contain("self.get_cranelift_local(local)")
expect(source).to_contain("self.compile_cranelift_binop(op, lv, rv)")
expect(source).to_contain("self.compile_cranelift_unaryop(op, v)")
expect(source).to_contain("codegen.compile_cranelift_function(fn_)")
expect(source).to_not_contain("self.compile_terminator(block.terminator)")
expect(source).to_not_contain("self.compile_const(value, type_)")
expect(source).to_not_contain("self.get_local(local)")
expect(source).to_not_contain("self.compile_binop(op, lv, rv)")
expect(source).to_not_contain("self.compile_unaryop(op, v)")
expect(source).to_not_contain("codegen.compile_function(fn_)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/host_gpu_lane_codegen_marker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Host/GPU lane native codegen markers.
- Host/GPU lane native codegen markers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f3848bc8da028ff08fad2dbbdcd00c039753a1c5214f2dbbce8cbf1f567b89f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f3848bc8da028ff08fad2dbbdcd00c039753a1c5214f2dbbce8cbf1f567b89f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f3848bc8da028ff08fad2dbbdcd00c039753a1c5214f2dbbce8cbf1f567b89f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/codegen/host_gpu_lane_codegen_marker_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/host_gpu_lane_codegen_marker_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/host_gpu_lane_codegen_marker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/host_gpu_lane_codegen_marker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/host_gpu_lane_codegen_marker_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/codegen/host_gpu_lane_codegen_marker_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'consumes lane markers as queue-boundary accounting instead of unsupported instructions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/host_gpu_lane_codegen_marker_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'diagnoses an unmatched host GPU lane end marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/host_gpu_lane_codegen_marker_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps Cranelift helper calls uniquely named for bootstrap dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
