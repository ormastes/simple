# Compiler Admission Specification

> Tests covering mission-critical exact-current compiler admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Admission Specification

## Scenarios

### mission-critical exact-current compiler admission

#### admits a complete hash-bound pure collector receipt

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits a complete hash-bound pure collector receipt
   - Expected: result.is_admitted() is true
   - Expected: result.rejection.name() equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("admits a complete hash-bound pure collector receipt")
val result = CompilerAdmissionV1.evaluate(valid_run(), artifact(), receipt())
expect(result.is_admitted()).to_equal(true)
expect(result.rejection.name()).to_equal("none")
```

</details>

#### rejects malformed and uppercase hash256 values

- rejects malformed and uppercase hash256 values
   - Expected: short_hash.rejection.name() equals `invalid_run_identity`
   - Expected: malformed.rejection.name() equals `invalid_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects malformed and uppercase hash256 values")
val short_hash = run_compiler_admission(valid_run(receipt_hash: "abc"), artifact(), receipt())
expect(short_hash.rejection.name()).to_equal("invalid_run_identity")
val uppercase = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
val malformed = run_compiler_admission(valid_run(), artifact(),
    receipt(source_hash: uppercase))
expect(malformed.rejection.name()).to_equal("invalid_hash")
```

</details>

#### rejects receipts not correlated to the release run

- rejects receipts not correlated to the release run
   - Expected: wrong_run.rejection.name() equals `run_correlation_mismatch`
   - Expected: wrong_receipt.rejection.name() equals `run_correlation_mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects receipts not correlated to the release run")
val wrong_run = run_compiler_admission(valid_run(), artifact(),
    receipt(run_id: "release-41"))
expect(wrong_run.rejection.name()).to_equal("run_correlation_mismatch")
val wrong_receipt = run_compiler_admission(valid_run(), artifact(),
    receipt(receipt_hash: H_PARENT))
expect(wrong_receipt.rejection.name()).to_equal("run_correlation_mismatch")
```

</details>

#### rejects receipt tampering without a matching canonical rehash

- rejects receipt tampering without a matching canonical rehash
   - Expected: result.rejection.name() equals `run_correlation_mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects receipt tampering without a matching canonical rehash")
val original = receipt()
val mutated = receipt(receipt_hash: original.receipt_hash,
    fixtures: [fixture(capture_hash: H_PARENT)])
val result = run_compiler_admission(valid_run(), artifact(), mutated)
expect(result.rejection.name()).to_equal("run_correlation_mismatch")
```

</details>

#### rejects parent identity not frozen by run policy

- rejects parent identity not frozen by run policy
   - Expected: result.rejection.name() equals `invalid_parent_lineage`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects parent identity not frozen by run policy")
var run = valid_run()
run.expected_parent_source_hash = H_PARENT
val result = run_compiler_admission(run, artifact(), receipt())
expect(result.rejection.name()).to_equal("invalid_parent_lineage")
```

</details>

#### rejects mismatched source and input evidence

- rejects mismatched source and input evidence
   - Expected: result.rejection.name() equals `input_identity_mismatch`
   - Expected: stale.rejection.name() equals `source_hash_mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects mismatched source and input evidence")
val wrong_source = receipt(source_hash: H_PARENT)
val result = run_compiler_admission(valid_run_for(wrong_source), artifact(),
    wrong_source)
expect(result.rejection.name()).to_equal("input_identity_mismatch")
val stale = run_compiler_admission(valid_run(),
    artifact(source_hash: H_PARENT), receipt())
expect(stale.rejection.name()).to_equal("source_hash_mismatch")
```

</details>

#### rejects bootstrap, hybrid, stale, and unknown compiler lineages

- rejects bootstrap, hybrid, stale, and unknown compiler lineages
   - Expected: run_compiler_admission(valid_run(), artifact(MciCompilerLineageV1.RustSeed), receipt()).rejection.name() equals `rust_seed_lineage`
   - Expected: run_compiler_admission(valid_run(), artifact(MciCompilerLineageV1.Hybrid), receipt()).rejection.name() equals `hybrid_lineage`
   - Expected: run_compiler_admission(valid_run(), artifact(MciCompilerLineageV1.Stale), receipt()).rejection.name() equals `stale_lineage`
   - Expected: run_compiler_admission(valid_run(), artifact(MciCompilerLineageV1.Unknown), receipt()).rejection.name() equals `unknown_lineage`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects bootstrap, hybrid, stale, and unknown compiler lineages")
expect(run_compiler_admission(valid_run(), artifact(MciCompilerLineageV1.RustSeed), receipt()).rejection.name()).to_equal("rust_seed_lineage")
expect(run_compiler_admission(valid_run(), artifact(MciCompilerLineageV1.Hybrid), receipt()).rejection.name()).to_equal("hybrid_lineage")
expect(run_compiler_admission(valid_run(), artifact(MciCompilerLineageV1.Stale), receipt()).rejection.name()).to_equal("stale_lineage")
expect(run_compiler_admission(valid_run(), artifact(MciCompilerLineageV1.Unknown), receipt()).rejection.name()).to_equal("unknown_lineage")
```

</details>

#### rejects missing pure-Simple parent lineage

- rejects missing pure-Simple parent lineage
   - Expected: result.rejection.name() equals `invalid_parent_lineage`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects missing pure-Simple parent lineage")
val result = run_compiler_admission(valid_run(),
    artifact(parent_lineage: MciCompilerLineageV1.RustSeed), receipt())
expect(result.rejection.name()).to_equal("invalid_parent_lineage")
```

</details>

#### rejects incomplete and extra fixture sets

- rejects incomplete and extra fixture sets
   - Expected: missing.rejection.name() equals `invalid_collector_receipt`
   - Expected: extra.rejection.name() equals `incomplete_fixture_set`
   - Expected: duplicate.rejection.name() equals `incomplete_fixture_set`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects incomplete and extra fixture sets")
val missing = run_compiler_admission(valid_run(), artifact(), receipt(fixtures: []))
expect(missing.rejection.name()).to_equal("invalid_collector_receipt")
val extra_receipt = receipt(fixtures: [fixture(), fixture()])
val extra = run_compiler_admission(valid_run_for(extra_receipt), artifact(),
    extra_receipt)
expect(extra.rejection.name()).to_equal("incomplete_fixture_set")
val duplicate_receipt = receipt(fixtures: [fixture(), fixture()])
val duplicate = run_compiler_admission(valid_run_for(duplicate_receipt,
    fixtures: [expected_fixture(), expected_fixture()]), artifact(), duplicate_receipt)
expect(duplicate.rejection.name()).to_equal("incomplete_fixture_set")
```

</details>

#### rejects fixture command timeout exit capture executable and function mismatches

- rejects fixture command timeout exit capture executable and function mismatches
   - Expected: run_compiler_admission(valid_run_for(wrong_command), artifact(), wrong_command).rejection.name() equals `non_discriminating_fixture`
   - Expected: run_compiler_admission(valid_run_for(wrong_timeout), artifact(), wrong_timeout).rejection.name() equals `fixture_not_executed`
   - Expected: run_compiler_admission(valid_run_for(wrong_exit), artifact(), wrong_exit).rejection.name() equals `fixture_failed`
   - Expected: run_compiler_admission(valid_run_for(wrong_capture), artifact(), wrong_capture).rejection.name() equals `non_discriminating_fixture`
   - Expected: run_compiler_admission(valid_run_for(wrong_executable), artifact(), wrong_executable).rejection.name() equals `non_executable_fixture`
   - Expected: run_compiler_admission(valid_run_for(wrong_function_count), artifact(), wrong_function_count).rejection.name() equals `missing_function_evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects fixture command timeout exit capture executable and function mismatches")
val wrong_command = receipt(fixtures: [fixture(command_hash: H_PARENT)])
expect(run_compiler_admission(valid_run_for(wrong_command), artifact(), wrong_command).rejection.name()).to_equal("non_discriminating_fixture")
val wrong_timeout = receipt(fixtures: [fixture(timeout_ms: 1)])
expect(run_compiler_admission(valid_run_for(wrong_timeout), artifact(), wrong_timeout).rejection.name()).to_equal("fixture_not_executed")
val wrong_exit = receipt(fixtures: [fixture(exit_code: 7)])
expect(run_compiler_admission(valid_run_for(wrong_exit), artifact(), wrong_exit).rejection.name()).to_equal("fixture_failed")
val wrong_capture = receipt(fixtures: [fixture(capture_hash: H_PARENT)])
expect(run_compiler_admission(valid_run_for(wrong_capture), artifact(), wrong_capture).rejection.name()).to_equal("non_discriminating_fixture")
val wrong_executable = receipt(fixtures: [fixture(executable_hash: H_PARENT)])
expect(run_compiler_admission(valid_run_for(wrong_executable), artifact(), wrong_executable).rejection.name()).to_equal("non_executable_fixture")
val wrong_function_count = receipt(fixtures: [fixture(function_count: 0)])
expect(run_compiler_admission(valid_run_for(wrong_function_count), artifact(), wrong_function_count).rejection.name()).to_equal("missing_function_evidence")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mission_critical/compiler_admission_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering mission-critical exact-current compiler admission.
- mission-critical exact-current compiler admission

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `907e7d95d2aa39f3b19ba481b3e3f3032dac5a562779bf70641b31fe4ba4ed76`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `907e7d95d2aa39f3b19ba481b3e3f3032dac5a562779bf70641b31fe4ba4ed76`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `907e7d95d2aa39f3b19ba481b3e3f3032dac5a562779bf70641b31fe4ba4ed76`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mission_critical/compiler_admission_spec.spl
mirror: doc/06_spec/01_unit/compiler/mission_critical/compiler_admission_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mission_critical/compiler_admission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mission_critical/compiler_admission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mission_critical/compiler_admission_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits a complete hash-bound pure collector receipt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mission_critical/compiler_admission_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects malformed and uppercase hash256 values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mission_critical/compiler_admission_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects receipts not correlated to the release run' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
