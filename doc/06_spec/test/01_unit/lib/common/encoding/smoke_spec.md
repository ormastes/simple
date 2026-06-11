# Smoke Specification

> <details>

<!-- sdn-diagram:id=smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smoke_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smoke Specification

## Scenarios

### impl smoke

#### encode varint 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = pb_encode_varint(1)
expect(enc.len()).to_equal(1)
```

</details>

#### decode field fixed64

1. var tb = pb encode tag
2. var vb = pb encode fixed64
3. var bv: u8 = tb[i] to i64
4. out push
5. var bv: u8 = vb[i] to i64
6. out push
   - Expected: r[2] equals `1000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tb = pb_encode_tag(4, 1)
var vb = pb_encode_fixed64(1000000000000)
var out: [u8] = []
var i = 0
while i < tb.len():
    var bv: u8 = tb[i].to_i64().to_u8()
    out.push(bv)
    i = i + 1
i = 0
while i < vb.len():
    var bv: u8 = vb[i].to_i64().to_u8()
    out.push(bv)
    i = i + 1
val r = pb_decode_field(out, 0)
expect(r[2]).to_equal(1000000000000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- impl smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
