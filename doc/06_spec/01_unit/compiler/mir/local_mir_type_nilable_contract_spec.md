# Local Mir Type Nilable Contract Specification

> Tests covering MIR local type nilable contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Local Mir Type Nilable Contract Specification

## Scenarios

### MIR local type nilable contract

#### returns a bare MIR type instead of an Option wrapper

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns a bare MIR type instead of an Option wrapper
   - Expected: is_bool_ptr is true
   - Expected: source does not contain `return Some(item.type_)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns a bare MIR type instead of an Option wrapper")
var lowering = MirLowering.new(SymbolTable.new())
var builder = lowering.builder
val local = builder.new_local(nil, MirType.bool(), LocalKind.Temp)
lowering.builder = builder

var observed = MirType.i64()
val found = lowering.local_mir_type_of(local)
if found != nil:
    observed = found
val ptr = MirType.ptr(observed, false)
val is_bool_ptr = match ptr.kind:
    case MirTypeKind.Ptr(pointee, _):
        match pointee.kind:
            case MirTypeKind.Bool: true
            case _: false
    case _: false
expect(is_bool_ptr).to_equal(true)

val source = rt_file_read_text("src/compiler/50.mir/mir_lowering_stmts.spl") ?? ""
expect(source).to_contain("return item.type_")
expect(source.contains("return Some(item.type_)")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/local_mir_type_nilable_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR local type nilable contract.
- MIR local type nilable contract

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
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5e9f8275f5fbb579bf2c76123a7e28d6df11c3e64d3165810c18e96c2a4f2710`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e9f8275f5fbb579bf2c76123a7e28d6df11c3e64d3165810c18e96c2a4f2710`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e9f8275f5fbb579bf2c76123a7e28d6df11c3e64d3165810c18e96c2a4f2710`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/mir/local_mir_type_nilable_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/local_mir_type_nilable_contract_spec.md (current)
findings: 5 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/mir/local_mir_type_nilable_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/local_mir_type_nilable_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/local_mir_type_nilable_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/mir/local_mir_type_nilable_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/mir/local_mir_type_nilable_contract_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a bare MIR type instead of an Option wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
