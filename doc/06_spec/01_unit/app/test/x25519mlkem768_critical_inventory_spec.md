# x25519mlkem768_critical_inventory_spec

> Operator-facing calibration contract for the hybrid-KEX critical-branch

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x25519mlkem768_critical_inventory_spec

Operator-facing calibration contract for the hybrid-KEX critical-branch

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test/x25519mlkem768_critical_inventory_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Operator-facing calibration contract for the hybrid-KEX critical-branch
    inventory. Audience: SIMD/GPU acceleration-lane owners and release
    engineers gating X25519+ML-KEM on decision-condition coverage. Scope:
    calibrating the symbolic critical-branch snapshot against the raw coverage
    report so every owner file, decision, and true/false outcome pair carries a
    concrete compiler identity. Assumptions: the thirty-owner snapshot and the
    decision-condition-v1 coverage report format are frozen.

## Scenarios

### X25519MLKEM768 critical branch inventory calibrator

#### should derive concrete compiler identities for the exact thirty-owner snapshot

- calibrate the thirty-owner snapshot and check every identity row is emitted


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-X25519MLKEM768-CRITICAL-INVENTORY
step("calibrate the thirty-owner snapshot and check every identity row is emitted")
val result = x25519_mlkem768_calibrate_critical_inventory_from_text(
    symbolic(), measured_raw(), source_hashes(), source_hashes(), source_texts())
expect(result.is_ok()).to_be(true)
val inventory = result.unwrap()
expect(inventory).to_start_with(
    "owner|source_path|line|decision_id|condition_id|outcome\n")
expect(inventory).to_contain(
    "cache_identity|src/os/crypto/x25519_mlkem768/cache_identity.spl|1|100|0|true")
val ids = owner_ids()
val paths = owner_paths()
var index: i64 = 0
while index < ids.len():
    val decision_id = (100 + index).to_text()
    val prefix = ids[index] + "|" + paths[index] + "|1|" + decision_id + "|0|"
    expect(inventory).to_contain(prefix + "true")
    expect(inventory).to_contain(prefix + "false")
    index = index + 1
```

</details>

#### should reject stale owner hashes and exact source anchors

- tamper an owner hash and a source anchor, then calibrate
   - Expected: stale_hash.unwrap_err() equals `symbolic-owner-source-sha256-stale`
   - Expected: stale_anchor.unwrap_err() equals `symbolic-source-anchor-stale`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-X25519MLKEM768-CRITICAL-INVENTORY
step("tamper an owner hash and a source anchor, then calibrate")
var stale_hashes = source_hashes()
stale_hashes[owner_paths()[0]] =
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
val stale_hash = x25519_mlkem768_calibrate_critical_inventory_from_text(
    symbolic(), measured_raw(), stale_hashes, source_hashes(), source_texts())
expect(stale_hash.is_err()).to_be(true)
expect(stale_hash.unwrap_err()).to_equal("symbolic-owner-source-sha256-stale")
val stale_anchor = x25519_mlkem768_calibrate_critical_inventory_from_text(
    symbolic().replace("|1|if critical:|0|true", "|2|if critical:|0|true"),
    measured_raw(), source_hashes(), source_hashes(), source_texts())
expect(stale_anchor.is_err()).to_be(true)
expect(stale_anchor.unwrap_err()).to_equal("symbolic-source-anchor-stale")
```

</details>

#### should reject stale decision linkage, condition identity, and uncovered outcomes

- tamper decision linkage, condition id, and an outcome count, then calibrate
   - Expected: stale_decision.unwrap_err() equals `raw-condition-decision-stale`
   - Expected: stale_condition.unwrap_err() equals `symbolic-condition-stale`
   - Expected: uncovered.unwrap_err() equals `symbolic-outcome-uncovered`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-X25519MLKEM768-CRITICAL-INVENTORY
step("tamper decision linkage, condition id, and an outcome count, then calibrate")
val stale_decision = x25519_mlkem768_calibrate_critical_inventory_from_text(
    symbolic(), measured_raw().replace(
        "100, 0, src/os/crypto/x25519_mlkem768/cache_identity.spl",
        "999, 0, src/os/crypto/x25519_mlkem768/cache_identity.spl"),
    source_hashes(), source_hashes(), source_texts())
expect(stale_decision.is_err()).to_be(true)
expect(stale_decision.unwrap_err()).to_equal("raw-condition-decision-stale")
val stale_condition = x25519_mlkem768_calibrate_critical_inventory_from_text(
    symbolic(), measured_raw().replace(
        "100, 0, src/os/crypto/x25519_mlkem768/cache_identity.spl",
        "100, 7, src/os/crypto/x25519_mlkem768/cache_identity.spl"),
    source_hashes(), source_hashes(), source_texts())
expect(stale_condition.is_err()).to_be(true)
expect(stale_condition.unwrap_err()).to_equal("symbolic-condition-stale")
val uncovered = x25519_mlkem768_calibrate_critical_inventory_from_text(
    symbolic(), measured_raw().replace(
        "100, 0, src/os/crypto/x25519_mlkem768/cache_identity.spl, 1, 1, 1, 1",
        "100, 0, src/os/crypto/x25519_mlkem768/cache_identity.spl, 1, 1, 1, 0"),
    source_hashes(), source_hashes(), source_texts())
expect(uncovered.is_err()).to_be(true)
expect(uncovered.unwrap_err()).to_equal("symbolic-outcome-uncovered")
```

</details>

#### should reject incomplete owner and true-false requirement sets

- drop an owner row and a false outcome row, then calibrate
   - Expected: missing_owner.unwrap_err() equals `symbolic-owner-set-incomplete`
   - Expected: missing_outcome.unwrap_err() equals `symbolic-outcome-pair-incomplete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-X25519MLKEM768-CRITICAL-INVENTORY
step("drop an owner row and a false outcome row, then calibrate")
val missing_owner = x25519_mlkem768_calibrate_critical_inventory_from_text(
    symbolic().replace(
        "owner|mlkem_ntt|src/os/crypto/ml_kem_ntt.spl|" + HASH_A + "\n", ""),
    measured_raw(), source_hashes(), source_hashes(), source_texts())
expect(missing_owner.is_err()).to_be(true)
expect(missing_owner.unwrap_err()).to_equal("symbolic-owner-set-incomplete")
val missing_outcome = x25519_mlkem768_calibrate_critical_inventory_from_text(
    symbolic().replace("critical|cache_identity|1|if critical:|0|false\n", ""),
    measured_raw(), source_hashes(), source_hashes(), source_texts())
expect(missing_outcome.is_err()).to_be(true)
expect(missing_outcome.unwrap_err()).to_equal("symbolic-outcome-pair-incomplete")
```

</details>

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

- `REQ-X25519MLKEM768-CRITICAL-INVENTORY`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `df3b8880c70ed5f93b74a2f261b61b38d992e764d8358da316b6b3cd6d57fdc6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `df3b8880c70ed5f93b74a2f261b61b38d992e764d8358da316b6b3cd6d57fdc6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `df3b8880c70ed5f93b74a2f261b61b38d992e764d8358da316b6b3cd6d57fdc6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: 01_unit/app/test/x25519mlkem768_critical_inventory_spec.spl
mirror: doc/06_spec/x25519mlkem768_critical_inventory_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/x25519mlkem768_critical_inventory_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/x25519mlkem768_critical_inventory_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/x25519mlkem768_critical_inventory_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/x25519mlkem768_critical_inventory_spec.spl:72:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should derive concrete compiler identities for the exact thirty-owner snapshot' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/x25519mlkem768_critical_inventory_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should derive concrete compiler identities for the exact thirty-owner snapshot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/x25519mlkem768_critical_inventory_spec.spl:93:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject stale owner hashes and exact source anchors' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/x25519mlkem768_critical_inventory_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject stale owner hashes and exact source anchors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/x25519mlkem768_critical_inventory_spec.spl:109:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject stale decision linkage, condition identity, and uncovered outcomes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/x25519mlkem768_critical_inventory_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject stale decision linkage, condition identity, and uncovered outcomes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/x25519mlkem768_critical_inventory_spec.spl:134:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject incomplete owner and true-false requirement sets' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
