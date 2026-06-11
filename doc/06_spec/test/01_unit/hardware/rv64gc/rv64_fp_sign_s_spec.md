# RV64 Single-Precision FP Sign Manipulation Tests

> Unit tests for fsgnj.s, fsgnjn.s, fsgnjx.s.

<!-- sdn-diagram:id=rv64_fp_sign_s_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_fp_sign_s_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_fp_sign_s_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_fp_sign_s_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Single-Precision FP Sign Manipulation Tests

Unit tests for fsgnj.s, fsgnjn.s, fsgnjx.s.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-SIGN-S-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_fp_sign_s_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for fsgnj.s, fsgnjn.s, fsgnjx.s.

## Scenarios

### FSGNJ.S (copy sign from rs2)

#### positive + positive = positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_sgnj_s(ONE_S, TWO_S)).to_equal(ONE_S)
```

</details>

#### positive + negative = negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_sgnj_s(ONE_S, NEG_TWO_S)).to_equal(NEG_ONE_S)
```

</details>

#### negative + positive = positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_sgnj_s(NEG_ONE_S, TWO_S)).to_equal(ONE_S)
```

</details>

### FSGNJN.S (copy negated sign from rs2)

#### positive + positive = negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_sgnjn_s(ONE_S, TWO_S)).to_equal(NEG_ONE_S)
```

</details>

#### positive + negative = positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_sgnjn_s(ONE_S, NEG_TWO_S)).to_equal(ONE_S)
```

</details>

#### negative + positive = negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_sgnjn_s(NEG_ONE_S, TWO_S)).to_equal(NEG_ONE_S)
```

</details>

### FSGNJX.S (XOR signs)

#### positive XOR positive = positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_sgnjx_s(ONE_S, TWO_S)).to_equal(ONE_S)
```

</details>

#### positive XOR negative = negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_sgnjx_s(ONE_S, NEG_TWO_S)).to_equal(NEG_ONE_S)
```

</details>

#### negative XOR negative = positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_sgnjx_s(NEG_ONE_S, NEG_TWO_S)).to_equal(ONE_S)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
