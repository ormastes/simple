# Simpleos Primary Tool Receipt V1 Specification

> Tests covering authenticated primary tool receipt.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Primary Tool Receipt V1 Specification

## Scenarios

### authenticated primary tool receipt

#### rejects a missing signature instead of promoting source presence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a missing signature instead of promoting source presence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a missing signature instead of promoting source presence")
val result = simpleos_primary_tool_receipt_verify_v1(
    receipt([]), "release-key-1", [], 150)
expect(result).to_be_err()
```

</details>

#### rejects expired and overlong admission windows before signature use

- rejects expired and overlong admission windows before signature use


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects expired and overlong admission windows before signature use")
val expired = simpleos_primary_tool_receipt_verify_v1(
    receipt([]), "release-key-1", [], 201)
expect(expired).to_be_err()
```

</details>

#### rejects a key id that is not the configured trust root

- rejects a key id that is not the configured trust root


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a key id that is not the configured trust root")
val result = simpleos_primary_tool_receipt_verify_v1(
    receipt([]), "another-key", [], 150)
expect(result).to_be_err()
```

</details>

#### changes canonical signed bytes when bound metadata is substituted

- changes canonical signed bytes when bound metadata is substituted


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("changes canonical signed bytes when bound metadata is substituted")
val original = receipt([])
val changed = SimpleOsPrimaryToolReceiptV1(
    schema_version: original.schema_version, tool_name: "ps",
    canonical_path: original.canonical_path,
    artifact_digest: original.artifact_digest,
    target_triple: original.target_triple, filesystem: original.filesystem,
    behavior_id: original.behavior_id, receipt_id: original.receipt_id,
    key_id: original.key_id, issued_unix_us: original.issued_unix_us,
    expires_unix_us: original.expires_unix_us, nonce: original.nonce,
    payload: original.payload, signature: original.signature)
expect(simpleos_primary_tool_receipt_canonical_body_v1(changed) == original.payload).to_be(false)
```

</details>

#### rejects a consumed receipt id and nonce before another admission

- rejects a consumed receipt id and nonce before another admission
   - Expected: replay.error equals `SimpleOsPrimaryToolReceiptError.Replayed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a consumed receipt id and nonce before another admission")
val original = receipt([])
val owner = SimpleOsPrimaryToolReceiptOwnerV1(
    consumed_keys: ["{original.receipt_id.len()}:{original.receipt_id}{original.nonce.len()}:{original.nonce}"])
val replay = simpleos_primary_tool_receipt_admit_v1(
    owner, original, "release-key-1", [], 150)
expect(replay.ok).to_be(false)
expect(replay.error).to_equal(SimpleOsPrimaryToolReceiptError.Replayed)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/contracts/execution/simpleos_primary_tool_receipt_v1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering authenticated primary tool receipt.
- authenticated primary tool receipt

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `8f8024226e8489c00b6a14ee77e67f2bbf1eff2c29eb9672ebabf1c0ee254bf8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8f8024226e8489c00b6a14ee77e67f2bbf1eff2c29eb9672ebabf1c0ee254bf8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8f8024226e8489c00b6a14ee77e67f2bbf1eff2c29eb9672ebabf1c0ee254bf8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/contracts/execution/simpleos_primary_tool_receipt_v1_spec.spl
mirror: doc/06_spec/01_unit/lib/common/contracts/execution/simpleos_primary_tool_receipt_v1_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/contracts/execution/simpleos_primary_tool_receipt_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/contracts/execution/simpleos_primary_tool_receipt_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/contracts/execution/simpleos_primary_tool_receipt_v1_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a missing signature instead of promoting source presence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contracts/execution/simpleos_primary_tool_receipt_v1_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects expired and overlong admission windows before signature use' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contracts/execution/simpleos_primary_tool_receipt_v1_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a key id that is not the configured trust root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
