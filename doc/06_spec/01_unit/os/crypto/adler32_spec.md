# Adler32 Specification

> <details>

<!-- sdn-diagram:id=adler32_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=adler32_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

adler32_spec -> std
adler32_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=adler32_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adler32 Specification

## Scenarios

### Adler-32 one-shot KATs

#### empty input -> 0x00000001 (A=1, B=0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(adler32(_empty())).to_equal(0x00000001)
```

</details>

#### \

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(adler32(_abc())).to_equal(0x024D0127)
```

</details>

#### \

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(adler32(_wikipedia())).to_equal(0x11E60398)
```

</details>

#### 6000-byte benchmark pattern crosses the classic 5552-byte reduction window

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(adler32(_pattern_6000())).to_equal(0x3B74AB6E)
```

</details>

### Adler-32 streaming API

#### update with empty data is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = 1
val s1 = adler32_update(s0, _empty())
expect(s1).to_equal(1)
```

</details>

#### split \

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = 1
val s1 = adler32_update(s0, _abc_first())
val s2 = adler32_update(s1, _abc_rest())
expect(s2).to_equal(adler32(_abc()))
```

</details>

#### full \

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = 1
val s1 = adler32_update(s0, _abc())
expect(s1).to_equal(0x024D0127)
```

</details>

### Fletcher-32 one-shot KATs

#### empty input -> 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fletcher32(_empty())).to_equal(0)
```

</details>

#### \

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fletcher32(_abcd())).to_equal(0x2926C6C4)
```

</details>

#### \

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fletcher32(_abc())).to_equal(0xC52562C4)
```

</details>

### Fletcher-32 streaming API

#### update with empty data is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fletcher32_update(0, 0, _empty())
expect(r[0]).to_equal(0)
expect(r[1]).to_equal(0)
```

</details>

#### split \

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = fletcher32_update(0, 0, _abcd_first())
val r2 = fletcher32_update(r1[0], r1[1], _abcd_rest())
val expected = fletcher32(_abcd())
expect((r2[1] << 16) | r2[0]).to_equal(expected)
```

</details>

#### full \

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fletcher32_update(0, 0, _abcd())
expect((r[1] << 16) | r[0]).to_equal(0x2926C6C4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/adler32_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Adler-32 one-shot KATs
- Adler-32 streaming API
- Fletcher-32 one-shot KATs
- Fletcher-32 streaming API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
