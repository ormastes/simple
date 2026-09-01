# Contract spec: test/01_unit/compiler/driver/native_cache_mir_fingerprint_prerequisite_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/driver/native_cache_mir_fingerprint_prerequisite_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/native_cache_mir_fingerprint_prerequisite_spec.spl` |
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
`bin/simple test test/01_unit/compiler/driver/native_cache_mir_fingerprint_prerequisite_spec.spl` and a green Results line.

## Scenarios

### native cache MIR fingerprint prerequisite

#### rejects incomplete MIR and dependency metadata as cache authority

- Expose the current non-canonical incomplete serializer
- Keep unsafe granular admission disabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
val serializer = file_read("src/compiler/50.mir/mir_serialization.spl")
val native_output = file_read("src/compiler/80.driver/driver_aot_native_output.spl")

step("Expose the current non-canonical incomplete serializer")
expect(serializer).to_contain("for func in module.functions.values():")
expect(serializer).to_not_contain("module.statics")        expect(serializer).to_not_contain("module.constants")        expect(serializer).to_not_contain("module.types")
step("Keep unsafe granular admission disabled")
expect(native_output).to_contain("build_cache.update_entry(cache_source, source_fp_val, [], [obj_path])")
expect(native_output).to_not_contain("mir_fingerprint")
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

- Canonical SPipe generation for source `5e34fbd8b3f1db0f112d357078c3b85e1040a125ae83e0ca6ae8064b04def04f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e34fbd8b3f1db0f112d357078c3b85e1040a125ae83e0ca6ae8064b04def04f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e34fbd8b3f1db0f112d357078c3b85e1040a125ae83e0ca6ae8064b04def04f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/compiler/driver/native_cache_mir_fingerprint_prerequisite_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/native_cache_mir_fingerprint_prerequisite_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/native_cache_mir_fingerprint_prerequisite_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: evidence
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/native_cache_mir_fingerprint_prerequisite_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/01_unit/compiler/driver/native_cache_mir_fingerprint_prerequisite_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects incomplete MIR and dependency metadata as cache authority' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
