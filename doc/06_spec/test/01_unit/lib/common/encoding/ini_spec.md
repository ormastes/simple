# Ini Specification

> <details>

<!-- sdn-diagram:id=ini_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ini_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ini_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ini_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ini Specification

## Scenarios

### INI parse — global keys

#### parses two global keys into two entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_global_key_count()).to_equal(2)
```

</details>

#### gets global key 'name'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_global_key_name()).to_equal("Alice")
```

</details>

#### gets global key 'age'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_global_key_age()).to_equal("30")
```

</details>

### INI parse — sections

#### parses two keys under [server] into two entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_section_key_count()).to_equal(2)
```

</details>

#### gets section key 'host'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_section_host()).to_equal("localhost")
```

</details>

#### gets section key 'port'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_section_port()).to_equal("8080")
```

</details>

#### skips semicolon comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_semicolon_comment_count()).to_equal(1)
```

</details>

#### skips hash comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_hash_comment_count()).to_equal(1)
```

</details>

#### trims spaces around = in value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_spaces_around_eq()).to_equal("spaced value")
```

</details>

#### parses key=value without spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_no_spaces_around_eq()).to_equal("nospace")
```

</details>

### INI parse — multiple sections

#### parses three entries across two sections

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_multiple_sections_count()).to_equal(3)
```

</details>

#### gets alpha.a

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_multiple_sections_alpha_a()).to_equal("1")
```

</details>

#### gets beta.b

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_multiple_sections_beta_b()).to_equal("2")
```

</details>

#### gets beta.c

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_multiple_sections_beta_c()).to_equal("3")
```

</details>

### INI get/set/remove

#### returns empty string for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_get_missing_returns_empty()).to_equal("")
```

</details>

#### updates existing entry value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_set_update_existing()).to_equal("new")
```

</details>

#### update does not change entry count

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_set_update_count_unchanged()).to_equal(1)
```

</details>

#### adds new entry when key not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_set_add_new_entry()).to_equal("newval")
```

</details>

#### add increments entry count

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_set_add_new_count()).to_equal(2)
```

</details>

#### removes entry decrements count

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_remove_entry_count()).to_equal(1)
```

</details>

#### removed entry returns empty on get

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_remove_entry_missing()).to_equal("")
```

</details>

#### removing nonexistent key leaves count unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_remove_nonexistent_count()).to_equal(1)
```

</details>

### INI sections and keys

#### lists two unique sections

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sections_count()).to_equal(2)
```

</details>

#### first section is 'alpha'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sections_first()).to_equal("alpha")
```

</details>

#### second section is 'beta'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sections_second()).to_equal("beta")
```

</details>

#### includes global section '' when global keys exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sections_includes_global()).to_equal(2)
```

</details>

#### lists three keys in section

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_keys_in_section_count()).to_equal(3)
```

</details>

#### first key in section is 'a'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_keys_in_section_first()).to_equal("a")
```

</details>

#### second key in section is 'b'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_keys_in_section_second()).to_equal("b")
```

</details>

### INI encode and round-trip

#### encoded output contains section header

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_encode_has_section_header()).to_equal(true)
```

</details>

#### encoded output contains key = value pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_encode_has_kv()).to_equal(true)
```

</details>

#### round-trip preserves entry count

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_roundtrip_count()).to_equal(3)
```

</details>

#### round-trip preserves alpha.a

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_roundtrip_alpha_a()).to_equal("1")
```

</details>

#### round-trip preserves alpha.b

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_roundtrip_alpha_b()).to_equal("2")
```

</details>

#### round-trip preserves beta.c

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_roundtrip_beta_c()).to_equal("3")
```

</details>

#### round-trip preserves section count

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_roundtrip_sections_count()).to_equal(2)
```

</details>

#### global keys encoded without section header

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_encode_global_no_header()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/ini_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- INI parse — global keys
- INI parse — sections
- INI parse — multiple sections
- INI get/set/remove
- INI sections and keys
- INI encode and round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
