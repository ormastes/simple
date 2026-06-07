# Http H3 Facade Specification

> <details>

<!-- sdn-diagram:id=http_h3_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=http_h3_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

http_h3_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=http_h3_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Http H3 Facade Specification

## Scenarios

### gc_async_mut http h3 facade

#### re-exports varint and frame helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = h3_varint_encode(64)
expect(encoded.length()).to_equal(2)
match h3_varint_decode(encoded, 0):
    case Ok(ok):
        expect(ok.value).to_equal(64)
        expect(ok.consumed).to_equal(2)
    case Err(msg):
        expect(msg).to_equal("")

val frame = h3_frame_emit(H3_FRAME_DATA, [1 as u8, 2 as u8])
match h3_frame_parse(frame, 0):
    case Ok(ok):
        expect(ok.frame_type).to_equal(H3_FRAME_DATA)
        expect(ok.payload.length()).to_equal(2)
    case Err(msg):
        expect(msg).to_equal("")

expect(H3_FRAME_SETTINGS).to_equal(4)
expect(H3_SETTINGS_MAX_FIELD_SECTION_SIZE).to_equal(6)
```

</details>

#### re-exports QPACK static table helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(qpack_static_table().length()).to_equal(99)
expect(qpack_static_lookup(25).value).to_equal("200")
expect(qpack_static_find_name(":method")).to_equal(15)
expect(qpack_static_find_exact(":status", "404")).to_equal(27)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/http/h3/http_h3_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut http h3 facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
