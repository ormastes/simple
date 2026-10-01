# Mir Instruction Split Contract Specification

> Tests covering split MIR instruction ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Instruction Split Contract Specification

## Scenarios

### split MIR instruction ownership

#### keeps the compatibility facade and owners bounded

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the compatibility facade and owners bounded


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the compatibility facade and owners bounded")
val facade = file_read("src/compiler/50.mir/mir_instructions.spl")
val support = file_read("src/compiler/50.mir/mir_instruction_support.spl")
val kinds = file_read("src/compiler/50.mir/mir_instruction_kinds.spl")
val graph = file_read("src/compiler/50.mir/mir_instruction_graph.spl")

expect(facade.len()).to_be_less_than(2000)
expect(support.len()).to_be_less_than(12000)
expect(kinds.len()).to_be_less_than(15000)
expect(graph.len()).to_be_less_than(9000)
```

</details>

#### constructs instructions and blocks through compatibility exports

- constructs instructions and blocks through compatibility exports
   - Expected: block.id.id equals `0`
   - Expected: block.instructions.len() equals `1`
   - Expected: int_value equals `41`
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("constructs instructions and blocks through compatibility exports")
val operand = mir_operand_const_int(41)
val inst = MirInst(
    kind: MirInstKind.Const(LocalId(id: 0), MirConstValue.Int(42), MirType.i64()),
    span: nil
)
val block = MirBlock(
    id: BlockId.entry(),
    label: Some("entry"),
    instructions: [inst],
    terminator: MirTerminator.Ret(Some(operand))
)

expect(block.id.id).to_equal(0)
expect(block.instructions.len()).to_equal(1)
match operand.kind:
    case MirOperandKind.Const(value, _):
        match value:
            case MirConstValue.Int(int_value):
                expect(int_value).to_equal(41)
            case _:
                expect(false).to_equal(true)
    case _:
        expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/mir_instruction_split_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering split MIR instruction ownership.
- split MIR instruction ownership

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `7282d86290234a26f1ca6de1e90a8bce7d07f64f7a76ce9891ccd5b64972009c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7282d86290234a26f1ca6de1e90a8bce7d07f64f7a76ce9891ccd5b64972009c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7282d86290234a26f1ca6de1e90a8bce7d07f64f7a76ce9891ccd5b64972009c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/mir/mir_instruction_split_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/mir_instruction_split_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/mir_instruction_split_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/mir_instruction_split_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/mir_instruction_split_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/mir_instruction_split_contract_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the compatibility facade and owners bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/mir_instruction_split_contract_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs instructions and blocks through compatibility exports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
