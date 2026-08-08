# X25519mlkem768 Critical Inventory Specification

> Tests covering X25519MLKEM768 critical branch inventory calibrator.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Critical Inventory Specification

## Scenarios

### X25519MLKEM768 critical branch inventory calibrator

#### should derive concrete compiler identities for the exact twenty-three-owner snapshot

- symbolic


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var stale hashes = source hashes
- stale hashes[owner paths
- symbolic
   - Expected: stale_hash.unwrap_err() equals `symbolic-owner-source-sha256-stale`
- symbolic
- measured raw
   - Expected: stale_anchor.unwrap_err() equals `symbolic-source-anchor-stale`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- symbolic
- source hashes
   - Expected: stale_decision.unwrap_err() equals `raw-condition-decision-stale`
- symbolic
- source hashes
   - Expected: stale_condition.unwrap_err() equals `symbolic-condition-stale`
- symbolic
- source hashes
   - Expected: uncovered.unwrap_err() equals `symbolic-outcome-uncovered`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- symbolic
- measured raw
   - Expected: missing_owner.unwrap_err() equals `symbolic-owner-set-incomplete`
- symbolic
- measured raw
   - Expected: missing_outcome.unwrap_err() equals `symbolic-outcome-pair-incomplete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test/x25519mlkem768_critical_inventory_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 critical branch inventory calibrator.
- X25519MLKEM768 critical branch inventory calibrator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
