# Buffer Specification

> <details>

<!-- sdn-diagram:id=buffer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=buffer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

buffer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=buffer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Buffer Specification

## Scenarios

### nogc_sync_mut io buffer

#### decodes buffered text without text.from_bytes

- Ok
   - Expected: text_value equals `ok?`
- Err
   - Expected: err.message equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = MemoryReader.new([111u8, 107u8, 255u8])
val reader = BufferedReader.with_capacity(raw, 2)
match reader.read_text():
    Ok(text_value):
        expect(text_value).to_equal("ok?")
    Err(err):
        expect(err.message).to_equal("")
```

</details>

#### decodes buffered lines without text.from_bytes

- Ok
   - Expected: text_value equals `ok\n`
- Err
   - Expected: err.message equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = MemoryReader.new([111u8, 107u8, 10u8])
val reader = BufferedReader.with_capacity(raw, 2)
match reader.read_line():
    Ok(text_value):
        expect(text_value).to_equal("ok\n")
    Err(err):
        expect(err.message).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/io/buffer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_sync_mut io buffer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
