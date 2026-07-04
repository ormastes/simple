# Seam Specification

> <details>

<!-- sdn-diagram:id=seam_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=seam_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

seam_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=seam_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Seam Specification

## Scenarios

### alpha_run_span

#### agreement: two closures returning the same ByteSpan yield that value

- fn
- fn
   - Expected: s.len() equals `4`
   - Expected: s.get(0).to_i64() equals `1`
   - Expected: s.get(1).to_i64() equals `2`
   - Expected: s.get(2).to_i64() equals `3`
   - Expected: s.get(3).to_i64() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Known 4-byte payload: [0x01, 0x02, 0x03, 0x04]
val known: [u8] = [1u8, 2u8, 3u8, 4u8]
val s = alpha_run_span(
    "test",
    "agree",
    fn(): ByteSpan.new(known),
    fn(): ByteSpan.new(known)
)
expect(s.len()).to_equal(4)
expect(s.get(0).to_i64()).to_equal(1)
expect(s.get(1).to_i64()).to_equal(2)
expect(s.get(2).to_i64()).to_equal(3)
expect(s.get(3).to_i64()).to_equal(4)
```

</details>

#### absent-oracle degradation: runtime empty, pure present -> returns pure, no halt

- fn
- fn
   - Expected: s.len() equals `4`
   - Expected: s.get(0).to_i64() equals `1`
   - Expected: s.get(3).to_i64() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When one backend is absent (returns []), alpha must NOT halt — it
# degrades to the present side. This guards the path every stubbed-runtime
# caller relies on; a regression here would abort real crypto calls.
val empty: [u8] = []
val known: [u8] = [1u8, 2u8, 3u8, 4u8]
val s = alpha_run_span(
    "test",
    "degrade",
    fn(): ByteSpan.new(empty),
    fn(): ByteSpan.new(known)
)
expect(s.len()).to_equal(4)
expect(s.get(0).to_i64()).to_equal(1)
expect(s.get(3).to_i64()).to_equal(4)
```

</details>

### alpha_run_digest

#### agreement: two closures returning the same ByteSpan yield that digest (ct_eq check)

- fn
- fn
   - Expected: d.len() equals `3`
   - Expected: d.ct_eq(expected) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Known 3-byte digest: 0x01 0x02 0x03
# Digest.hex() is broken cross-module (see file header); use ct_eq instead.
val known: [u8] = [1u8, 2u8, 3u8]
val d = alpha_run_digest(
    "test",
    "digest_agree",
    fn(): ByteSpan.new(known),
    fn(): ByteSpan.new(known)
)
val expected = Digest.new(known)
expect(d.len()).to_equal(3)
expect(d.ct_eq(expected)).to_equal(true)
```

</details>

#### absent-oracle degradation: runtime empty, pure present -> returns pure digest, no halt

- fn
- fn
   - Expected: d.len() equals `3`
   - Expected: d.ct_eq(expected) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Same degradation guard for the digest seam: a missing runtime backend
# must yield the pure digest, never an abort.
val empty: [u8] = []
val known: [u8] = [1u8, 2u8, 3u8]
val d = alpha_run_digest(
    "test",
    "digest_degrade",
    fn(): ByteSpan.new(empty),
    fn(): ByteSpan.new(known)
)
val expected = Digest.new(known)
expect(d.len()).to_equal(3)
expect(d.ct_eq(expected)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/typed/seam_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- alpha_run_span
- alpha_run_digest

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
