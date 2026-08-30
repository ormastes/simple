# String Helpers Hex Specification

> <details>

<!-- sdn-diagram:id=string_helpers_hex_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_helpers_hex_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_helpers_hex_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_helpers_hex_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Helpers Hex Specification

## Scenarios

### app.io.string_helpers

### hex_to_char

#### converts ASCII codes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_char(65)).to_equal("A")
expect(hex_to_char(97)).to_equal("a")
expect(hex_to_char(48)).to_equal("0")
```

</details>

#### converts zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = hex_to_char(0)
expect(result.len()).to_be_greater_than(0)
```

</details>

### byte_to_char

#### is alias for hex_to_char

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(byte_to_char(65)).to_equal("A")
expect(byte_to_char(90)).to_equal("Z")
```

</details>

### char_code

#### returns 0 for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("")).to_equal(0)
```

</details>

### text_hash_native

#### returns consistent hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = text_hash_native("hello")
val h2 = text_hash_native("hello")
expect(h1).to_equal(h2)
```

</details>

#### returns different hashes for different lengths

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = text_hash_native("a")
val h2 = text_hash_native("ab")
val same = h1 == h2
expect(same).to_equal(false)
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = text_hash_native("")
expect(h).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/string_helpers_hex_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- app.io.string_helpers
- hex_to_char
- byte_to_char
- char_code
- text_hash_native

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
