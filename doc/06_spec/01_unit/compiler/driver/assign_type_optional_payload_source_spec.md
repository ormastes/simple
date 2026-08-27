# Assignment Type Optional Payload Contract

> Prevents staged-native assignment lowering from dereferencing a lost HirType

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assignment Type Optional Payload Contract

Prevents staged-native assignment lowering from dereferencing a lost HirType

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/assign_type_optional_payload_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Prevents staged-native assignment lowering from dereferencing a lost HirType
payload after an Optional presence check.

## Scenarios

### Assignment Type Optional Payload

#### matches optional type payloads structurally and rejects raw zero

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches optional type payloads structurally and rejects raw zero
   - Expected: source does not contain `if found_declared_type.?:`
   - Expected: source does not contain `found_declared_type ?? HirType`
   - Expected: source does not contain `if found_assigned_hir_type.?:`
   - Expected: source does not contain `found_assigned_hir_type ?? HirType`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches optional type payloads structurally and rejects raw zero")
val source = rt_file_read_text(
    "src/compiler/50.mir/mir_lowering_stmts.spl") ?? ""
expect(source).to_contain("match found_declared_type:")
expect(source).to_contain("declared_type != nil and declared_type != 0")
expect(source).to_contain("match found_assigned_hir_type:")
expect(source).to_contain("assigned_hir_type != nil and assigned_hir_type != 0")
expect(source.contains("if found_declared_type.?:")).to_equal(false)
expect(source.contains("found_declared_type ?? HirType")).to_equal(false)
expect(source.contains("if found_assigned_hir_type.?:")).to_equal(false)
expect(source.contains("found_assigned_hir_type ?? HirType")).to_equal(false)
```

</details>

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

- Canonical SPipe generation for source `34c77ceb1d4b210d524af8c087c01bf40b506f5be6e204f0f3e18c13e1c6377a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `34c77ceb1d4b210d524af8c087c01bf40b506f5be6e204f0f3e18c13e1c6377a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `34c77ceb1d4b210d524af8c087c01bf40b506f5be6e204f0f3e18c13e1c6377a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/driver/assign_type_optional_payload_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/assign_type_optional_payload_source_spec.md (current)
findings: 5 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/driver/assign_type_optional_payload_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/assign_type_optional_payload_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/assign_type_optional_payload_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/driver/assign_type_optional_payload_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/driver/assign_type_optional_payload_source_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches optional type payloads structurally and rejects raw zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
