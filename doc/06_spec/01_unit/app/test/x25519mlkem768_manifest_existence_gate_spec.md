# x25519mlkem768_manifest_existence_gate_spec

> Operator-facing existence gate for the two X25519MLKEM768 campaign

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x25519mlkem768_manifest_existence_gate_spec

Operator-facing existence gate for the two X25519MLKEM768 campaign

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test/x25519mlkem768_manifest_existence_gate_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Operator-facing existence gate for the two X25519MLKEM768 campaign
    manifests. Audience: coverage-campaign owners and release engineers.
    Scope: every manifest-listed path exists on disk, each path is listed
    exactly once, declared blocks stay enumerated and retire when their gap
    lands. Assumptions: the critical inventory's owner list delegates to the
    coverage contract's, so gating the contract gates both manifests.

## Scenarios

### X25519MLKEM768 campaign manifest existence gate

#### should prove the checker can go RED on a path that is not on disk

- Feed a phantom path to the absence checker


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-X25519MLKEM768-MANIFEST-GATE
step("Feed a phantom path to the absence checker")
"""A phantom path must be reported, otherwise the gate is fail-open and
every green result below would be meaningless."""
val phantom = "src/app/test/no_such_manifest_entry_exists.spl"
val absent = x25519_mlkem768_coverage_absent_in([phantom])
assert_equal(absent.len(), 1)
assert_equal(absent[0], phantom)
```

</details>

#### should not report a path that does exist

- Check the coverage-contract module itself for absence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-X25519MLKEM768-MANIFEST-GATE
step("Check the coverage-contract module itself for absence")
val absent = x25519_mlkem768_coverage_absent_in(
    ["src/app/test/x25519mlkem768_coverage_contract.spl"])
assert_equal(absent.len(), 0)
```

</details>

#### should list every declared coverage-contract path exactly once

- Walk the contract manifest and reject duplicates


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-X25519MLKEM768-MANIFEST-GATE
step("Walk the contract manifest and reject duplicates")
val paths = x25519_mlkem768_coverage_manifest_paths()
assert_equal(paths.len(), 37)
var seen: [text] = []
for path in paths:
    assert_false(seen.contains(path))
    seen.push(path)
```

</details>

#### should list every declared critical-inventory path exactly once

- Walk the inventory manifest and reject duplicates


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-X25519MLKEM768-MANIFEST-GATE
step("Walk the inventory manifest and reject duplicates")
val paths = critical_manifest_paths()
assert_equal(paths.len(), 24)
var seen: [text] = []
for path in paths:
    assert_false(seen.contains(path))
    seen.push(path)
```

</details>

#### should find no unexpectedly absent path in the coverage contract

- Report absent contract manifest paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-X25519MLKEM768-MANIFEST-GATE
step("Report absent contract manifest paths")
val absent = x25519_mlkem768_coverage_manifest_absent_paths()
print x25519_mlkem768_coverage_manifest_gate_report()
assert_equal(absent.join(","), "")
```

</details>

#### should find no unexpectedly absent path in the critical inventory

- Report absent inventory manifest paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-X25519MLKEM768-MANIFEST-GATE
step("Report absent inventory manifest paths")
val absent = x25519_mlkem768_coverage_absent_in(critical_manifest_paths())
print "critical-inventory manifest-existence-gate: absent={absent.len()}"
assert_equal(absent.join(","), "")
```

</details>

#### should retire a declared block once the module lands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stale = x25519_mlkem768_coverage_stale_blocked_paths()
assert_equal(stale.join(","), "")
```

</details>

#### should keep every declared-blocked path named inside a manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for path in x25519_mlkem768_coverage_declared_blocked_paths():
    assert_true(x25519_mlkem768_coverage_manifest_paths().contains(path))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-X25519MLKEM768-MANIFEST-GATE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b75b5a0bb4f3088db67622a733b7ae8e7f5f4eff1ff04981954903adf3c5ac30`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b75b5a0bb4f3088db67622a733b7ae8e7f5f4eff1ff04981954903adf3c5ac30`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b75b5a0bb4f3088db67622a733b7ae8e7f5f4eff1ff04981954903adf3c5ac30`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: 01_unit/app/test/x25519mlkem768_manifest_existence_gate_spec.spl
mirror: doc/06_spec/x25519mlkem768_manifest_existence_gate_spec.md (current)
findings: 14 blockers: 0
  narrative=100 structure=50 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/x25519mlkem768_manifest_existence_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/x25519mlkem768_manifest_existence_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/x25519mlkem768_manifest_existence_gate_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/x25519mlkem768_manifest_existence_gate_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should prove the checker can go RED on a path that is not on disk' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/x25519mlkem768_manifest_existence_gate_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should prove the checker can go RED on a path that is not on disk' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/x25519mlkem768_manifest_existence_gate_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should not report a path that does exist' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/x25519mlkem768_manifest_existence_gate_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should not report a path that does exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/x25519mlkem768_manifest_existence_gate_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should list every declared coverage-contract path exactly once' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/x25519mlkem768_manifest_existence_gate_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should list every declared coverage-contract path exactly once' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/x25519mlkem768_manifest_existence_gate_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should list every declared critical-inventory path exactly once' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/x25519mlkem768_manifest_existence_gate_spec.spl:91:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should find no unexpectedly absent path in the coverage contract' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/x25519mlkem768_manifest_existence_gate_spec.spl:98:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should find no unexpectedly absent path in the critical inventory' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/x25519mlkem768_manifest_existence_gate_spec.spl:105:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should retire a declared block once the module lands' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/x25519mlkem768_manifest_existence_gate_spec.spl:111:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should keep every declared-blocked path named inside a manifest' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
