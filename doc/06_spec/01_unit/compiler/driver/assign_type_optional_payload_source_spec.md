# Contract spec: test/01_unit/compiler/driver/assign_type_optional_payload_source_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/driver/assign_type_optional_payload_source_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/assign_type_optional_payload_source_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/driver/assign_type_optional_payload_source_spec.spl` and a green Results line.

## Scenarios

### Assignment Type Optional Payload

#### matches optional type payloads structurally and rejects raw zero

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches optional type payloads structurally and rejects raw zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
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
expect(source).to_not_contain("if found_declared_type.?:")        expect(source).to_not_contain("found_declared_type ?? HirType")        expect(source).to_not_contain("if found_assigned_hir_type.?:")        expect(source).to_not_contain("found_assigned_hir_type ?? HirType")
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1deece4fdea46f1535999e66d672bfdce0ef102ef092e9c123a9f2941c4c1748`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1deece4fdea46f1535999e66d672bfdce0ef102ef092e9c123a9f2941c4c1748`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1deece4fdea46f1535999e66d672bfdce0ef102ef092e9c123a9f2941c4c1748`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **98/100**; effective score: **98/100**; blockers: **0**.

SSpec documentization score: 98/100
source: test/01_unit/compiler/driver/assign_type_optional_payload_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/assign_type_optional_payload_source_spec.md (current)
findings: 1 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/driver/assign_type_optional_payload_source_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches optional type payloads structurally and rejects raw zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
