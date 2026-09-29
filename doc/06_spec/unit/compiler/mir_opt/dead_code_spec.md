# Dead Code Specification

> Tests covering MIR Dead Code Elimination.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dead Code Specification

## Scenarios

### MIR Dead Code Elimination

#### identifies itself as a transform pass with no dependencies

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- identifies itself as a transform pass with no dependencies
   - Expected: dce.name() equals `dead_code_elimination`
   - Expected: dce.is_analysis_pass() is false
   - Expected: dce.dependencies().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies itself as a transform pass with no dependencies")
var dce = create_dce_pass()

expect(dce.name()).to_equal("dead_code_elimination")
expect(dce.is_analysis_pass()).to_equal(false)
expect(dce.dependencies().len()).to_equal(0)
```

</details>

#### treats stores and calls as side-effecting but plain copies as pure

- treats stores and calls as side-effecting but plain copies as pure


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats stores and calls as side-effecting but plain copies as pure")
var dce = create_dce_pass()

expect(dce.instruction_has_side_effects(
    _dce_inst(MirInstKind.Store(_dce_copy(1), _dce_copy(2))))).to_equal(true)
expect(dce.instruction_has_side_effects(
    _dce_inst(MirInstKind.CheckedBinOp(_dce_lid(3), MirBinOp.Add, _dce_copy(1), _dce_copy(2))))).to_equal(true)
expect(dce.instruction_has_side_effects(
    _dce_inst(MirInstKind.Copy(_dce_lid(3), _dce_lid(1))))).to_equal(false)
```

</details>

#### keeps impure intrinsics but not pure math intrinsics

- keeps impure intrinsics but not pure math intrinsics
   - Expected: dce.is_pure_intrinsic("sqrt") is true
   - Expected: dce.is_pure_intrinsic("abs") is true
   - Expected: dce.is_pure_intrinsic("print") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps impure intrinsics but not pure math intrinsics")
var dce = create_dce_pass()

expect(dce.is_pure_intrinsic("sqrt")).to_equal(true)
expect(dce.is_pure_intrinsic("abs")).to_equal(true)
expect(dce.is_pure_intrinsic("print")).to_equal(false)
expect(dce.instruction_has_side_effects(
    _dce_inst(MirInstKind.Intrinsic(Some(_dce_lid(4)), "sqrt", [_dce_copy(1)])))).to_equal(false)
expect(dce.instruction_has_side_effects(
    _dce_inst(MirInstKind.Intrinsic(Some(_dce_lid(4)), "print", [_dce_copy(1)])))).to_equal(true)
```

</details>

#### runs in every optimized pipeline level

- runs in every optimized pipeline level
   - Expected: optimizationpipeline_passes_for_level(OptLevel.Speed).index_of("dead_code_elimination") >= 0 is true
   - Expected: optimizationpipeline_passes_for_level(OptLevel.Aggressive).index_of("dead_code_elimination") >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs in every optimized pipeline level")
expect(optimizationpipeline_passes_for_level(OptLevel.Speed).index_of("dead_code_elimination") >= 0).to_equal(true)
expect(optimizationpipeline_passes_for_level(OptLevel.Aggressive).index_of("dead_code_elimination") >= 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/mir_opt/dead_code_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR Dead Code Elimination.
- MIR Dead Code Elimination

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

- Canonical SPipe generation for source `cccddea907ba8b355eefa6e6f0a7b9dc14d43c166348be5a958e3107328c0ad2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cccddea907ba8b355eefa6e6f0a7b9dc14d43c166348be5a958e3107328c0ad2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cccddea907ba8b355eefa6e6f0a7b9dc14d43c166348be5a958e3107328c0ad2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/mir_opt/dead_code_spec.spl
mirror: doc/06_spec/unit/compiler/mir_opt/dead_code_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/mir_opt/dead_code_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/mir_opt/dead_code_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/mir_opt/dead_code_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/mir_opt/dead_code_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies itself as a transform pass with no dependencies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir_opt/dead_code_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats stores and calls as side-effecting but plain copies as pure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir_opt/dead_code_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps impure intrinsics but not pure math intrinsics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
