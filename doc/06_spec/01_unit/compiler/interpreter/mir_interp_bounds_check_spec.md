# Mir Interp Bounds Check Specification

> Tests covering MIR interpreter bounds_check intrinsic.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Interp Bounds Check Specification

## Scenarios

### MIR interpreter bounds_check intrinsic

#### traps loudly on an out-of-bounds index instead of returning a value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- traps loudly on an out-of-bounds index instead of returning a value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("traps loudly on an out-of-bounds index instead of returning a value")
var interp = MirInterpreter.create()
# index 5, len 3 -> OOB. Native path PANICs; interpreter must error too.
val inst = bc_inst(Some(bc_local(1)), [mir_operand_const_int(5), mir_operand_const_int(3)])
val err = interp.execute_instruction(inst)
expect(err.unwrap().message()).to_contain("out of bounds")
```

</details>

#### traps loudly on a negative index

- traps loudly on a negative index


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("traps loudly on a negative index")
var interp = MirInterpreter.create()
val inst = bc_inst(Some(bc_local(1)), [mir_operand_const_int(-1), mir_operand_const_int(3)])
val err = interp.execute_instruction(inst)
expect(err.unwrap().message()).to_contain("out of bounds")
```

</details>

#### traps even when lowering discarded the dest

- traps even when lowering discarded the dest


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("traps even when lowering discarded the dest")
var interp = MirInterpreter.create()
# No dest: previously the 1 "failure" result was fully discarded.
val inst = bc_inst(nil, [mir_operand_const_int(9), mir_operand_const_int(3)])
val err = interp.execute_instruction(inst)
expect(err.unwrap().message()).to_contain("out of bounds")
```

</details>

#### traps on a malformed bounds_check with missing args

- traps on a malformed bounds_check with missing args


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("traps on a malformed bounds_check with missing args")
var interp = MirInterpreter.create()
val inst = bc_inst(Some(bc_local(1)), [mir_operand_const_int(0)])
val err = interp.execute_instruction(inst)
expect(err.unwrap().message()).to_contain("malformed")
```

</details>

#### passes an in-bounds index unchanged with no error

- passes an in-bounds index unchanged with no error
   - Expected: interp.get_local(bc_local(1)) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes an in-bounds index unchanged with no error")
var interp = MirInterpreter.create()
val inst = bc_inst(Some(bc_local(1)), [mir_operand_const_int(2), mir_operand_const_int(3)])
val err = interp.execute_instruction(inst)
expect(err).to_be_nil()
expect(interp.get_local(bc_local(1))).to_equal(0)
```

</details>

#### passes index zero of a non-empty array

- passes index zero of a non-empty array
   - Expected: interp.get_local(bc_local(1)) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes index zero of a non-empty array")
var interp = MirInterpreter.create()
val inst = bc_inst(Some(bc_local(1)), [mir_operand_const_int(0), mir_operand_const_int(1)])
val err = interp.execute_instruction(inst)
expect(err).to_be_nil()
expect(interp.get_local(bc_local(1))).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/mir_interp_bounds_check_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR interpreter bounds_check intrinsic.
- MIR interpreter bounds_check intrinsic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `6f3b14202da91b96681ddd2f60b750e52150e28e8ebfee3303451de1de9e5673`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6f3b14202da91b96681ddd2f60b750e52150e28e8ebfee3303451de1de9e5673`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6f3b14202da91b96681ddd2f60b750e52150e28e8ebfee3303451de1de9e5673`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/interpreter/mir_interp_bounds_check_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/mir_interp_bounds_check_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/mir_interp_bounds_check_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/mir_interp_bounds_check_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/mir_interp_bounds_check_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/mir_interp_bounds_check_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'traps loudly on an out-of-bounds index instead of returning a value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/mir_interp_bounds_check_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'traps loudly on a negative index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/mir_interp_bounds_check_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'traps even when lowering discarded the dest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
