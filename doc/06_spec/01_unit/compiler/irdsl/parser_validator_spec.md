# Parser Validator Specification

> Tests covering IRDSL parser and validator.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Validator Specification

## Scenarios

### IRDSL parser and validator

#### parses member-backed fields and validates partial backend errors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses member-backed fields and validates partial backend errors
   - Expected: instructions.len() equals `1`
   - Expected: instructions[0].name equals `Add`
   - Expected: instructions[0].params.len() equals `2`
   - Expected: validator.has_errors() is true
   - Expected: validator.error_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses member-backed fields and validates partial backend errors")
val source = "instruction Add:\n" +
    "params: lhs:i64, rhs:i64\n" +
    "backends: cranelift, llvm\n" +
    "description: Add two values\n" +
    "rust_pattern: Add(lhs, rhs)\n" +
    "category: arithmetic\n\n"
val instructions = parse_irdsl_file(source)

expect(instructions.len()).to_equal(1)
expect(instructions[0].name).to_equal("Add")
expect(instructions[0].params.len()).to_equal(2)
expect(instructions[0].backends).to_contain("llvm")
expect(validate_instructions(instructions)).to_contain("missing_error")

val validator = IrValidator(
    instructions: instructions,
    errors: []
)
validator.validate()
expect(validator.has_errors()).to_equal(true)
expect(validator.error_count()).to_equal(1)

val empty_coverage = check_coverage([])
expect(empty_coverage).to_contain("| Cranelift | 0/0 | 0% |")
expect(empty_coverage).to_contain("| Interpreter | 0/0 | 0% |")

val coverage = check_coverage(instructions)
expect(coverage).to_contain("| Cranelift | 1/1 | 100% |")
expect(coverage).to_contain("| LLVM | 1/1 | 100% |")
expect(coverage).to_contain("| Vulkan | 0/1 | 0% |")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/irdsl/parser_validator_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering IRDSL parser and validator.
- IRDSL parser and validator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `881f9cbfc56296f2f6c3130dbe76451fa738898ba6a6a590c99e05c9fe84744d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `881f9cbfc56296f2f6c3130dbe76451fa738898ba6a6a590c99e05c9fe84744d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `881f9cbfc56296f2f6c3130dbe76451fa738898ba6a6a590c99e05c9fe84744d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/irdsl/parser_validator_spec.spl
mirror: doc/06_spec/01_unit/compiler/irdsl/parser_validator_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/irdsl/parser_validator_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/irdsl/parser_validator_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/irdsl/parser_validator_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/irdsl/parser_validator_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses member-backed fields and validates partial backend errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
