# Static Table Specification

> <details>

<!-- sdn-diagram:id=static_table_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=static_table_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

static_table_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=static_table_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static Table Specification

## Scenarios

### HPACK static table

#### has exactly 61 entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hpack_static_table_size()).to_equal(61)
expect(hpack_static_table().len()).to_equal(61)
```

</details>

#### index 1 is :authority with empty value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = hpack_static_lookup(1)
expect(e.?).to_equal(true)
val entry = e ?? StaticEntry(name: "", value: "")
expect(entry.name).to_equal(":authority")
expect(entry.value).to_equal("")
```

</details>

#### index 2 is :method GET

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = hpack_static_lookup(2) ?? StaticEntry(name: "", value: "")
expect(entry.name).to_equal(":method")
expect(entry.value).to_equal("GET")
```

</details>

#### index 3 is :method POST

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = hpack_static_lookup(3) ?? StaticEntry(name: "", value: "")
expect(entry.name).to_equal(":method")
expect(entry.value).to_equal("POST")
```

</details>

#### index 7 is :scheme https

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = hpack_static_lookup(7) ?? StaticEntry(name: "", value: "")
expect(entry.name).to_equal(":scheme")
expect(entry.value).to_equal("https")
```

</details>

#### index 8 is :status 200

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = hpack_static_lookup(8) ?? StaticEntry(name: "", value: "")
expect(entry.name).to_equal(":status")
expect(entry.value).to_equal("200")
```

</details>

#### index 16 is accept-encoding 'gzip, deflate'

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = hpack_static_lookup(16) ?? StaticEntry(name: "", value: "")
expect(entry.name).to_equal("accept-encoding")
expect(entry.value).to_equal("gzip, deflate")
```

</details>

#### index 31 is content-type with empty value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = hpack_static_lookup(31) ?? StaticEntry(name: "", value: "")
expect(entry.name).to_equal("content-type")
expect(entry.value).to_equal("")
```

</details>

#### index 61 is www-authenticate with empty value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = hpack_static_lookup(61) ?? StaticEntry(name: "", value: "")
expect(entry.name).to_equal("www-authenticate")
expect(entry.value).to_equal("")
```

</details>

#### out-of-range indices return nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hpack_static_lookup(0).?).to_equal(false)
expect(hpack_static_lookup(62).?).to_equal(false)
expect(hpack_static_lookup(-1).?).to_equal(false)
```

</details>

### HPACK static table lookup

#### finds an exact (name, value) pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = hpack_static_find(":method", "GET")
expect(r.0).to_equal(2)
expect(r.1).to_equal(true)
```

</details>

#### finds :method POST at index 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = hpack_static_find(":method", "POST")
expect(r.0).to_equal(3)
expect(r.1).to_equal(true)
```

</details>

#### finds :status 404 at index 13

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = hpack_static_find(":status", "404")
expect(r.0).to_equal(13)
expect(r.1).to_equal(true)
```

</details>

#### returns name-only match for an unknown method

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# :method exists with values GET (idx 2) and POST (idx 3); first
# name-match wins, so index 2 is returned without value match.
val r = hpack_static_find(":method", "PUT")
expect(r.0).to_equal(2)
expect(r.1).to_equal(false)
```

</details>

#### returns name-only match for a header with no value variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# content-type only appears once with empty value; querying with a
# specific MIME yields name-only.
val r = hpack_static_find("content-type", "application/json")
expect(r.0).to_equal(31)
expect(r.1).to_equal(false)
```

</details>

#### finds the empty-value entry as an exact match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = hpack_static_find("content-type", "")
expect(r.0).to_equal(31)
expect(r.1).to_equal(true)
```

</details>

#### returns -1 for unknown header name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = hpack_static_find("x-custom-header", "value")
expect(r.0).to_equal(-1)
expect(r.1).to_equal(false)
```

</details>

#### is case-sensitive (HPACK requires lowercase names)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Caller is responsible for lowercasing; uppercase names do not match.
val r = hpack_static_find("CONTENT-TYPE", "")
expect(r.0).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/hpack/static_table_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HPACK static table
- HPACK static table lookup

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
