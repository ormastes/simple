# Manifest Specification

> <details>

<!-- sdn-diagram:id=manifest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=manifest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

manifest_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=manifest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Manifest Specification

## Scenarios

### Plugin manifest registry

#### parses a manifest with one plugin and two functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = parse_plugin_manifest_text(
    "plugins:\n" +
    "    -\n" +
    "        name: regex\n" +
    "        library: /tmp/libsimple_regex_ffi.so\n" +
    "        version: \"0.1.0\"\n" +
    "        functions: [rt_regex_new, rt_regex_destroy]\n"
)
expect(entries.len()).to_equal(1)
expect(entries[0].name).to_equal("regex")
expect(entries[0].functions.len()).to_equal(2)
expect(entries[0].functions[1]).to_equal("rt_regex_destroy")
```

</details>

#### renders manifest text for plugin entries

1. plugin entry new


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rendered = plugin_manifest_to_text([
    plugin_entry_new("http", "/tmp/libsimple_http_ffi.so", "0.2.0", ["rt_http_get"])
])
expect(rendered).to_contain("plugins:")
expect(rendered).to_contain("name: http")
expect(rendered).to_contain("functions: [rt_http_get]")
```

</details>

#### merges by plugin name and replaces existing entries

1. [plugin entry new
2. [plugin entry new
   - Expected: merged.len() equals `1`
   - Expected: merged[0].library equals `/new/lib.so`
   - Expected: merged[0].functions.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val merged = merge_plugin_entries(
    [plugin_entry_new("regex", "/old/lib.so", "0.1.0", ["rt_regex_new"])],
    [plugin_entry_new("regex", "/new/lib.so", "0.2.0", ["rt_regex_new", "rt_regex_destroy"])]
)
expect(merged.len()).to_equal(1)
expect(merged[0].library).to_equal("/new/lib.so")
expect(merged[0].functions.len()).to_equal(2)
```

</details>

#### removes a plugin by name

1. plugin entry new
2. plugin entry new
   - Expected: filtered.len() equals `1`
   - Expected: filtered[0].name equals `http`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val filtered = remove_plugin_entry(
    [
        plugin_entry_new("regex", "/tmp/regex.so", "0.1.0", ["rt_regex_new"]),
        plugin_entry_new("http", "/tmp/http.so", "0.1.0", ["rt_http_get"])
    ],
    "regex"
)
expect(filtered.len()).to_equal(1)
expect(filtered[0].name).to_equal("http")
```

</details>

#### rejects duplicate extern symbols across plugins

1. plugin entry new
2. plugin entry new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = validate_unique_symbols([
    plugin_entry_new("regex", "/tmp/regex.so", "0.1.0", ["rt_shared"]),
    plugin_entry_new("http", "/tmp/http.so", "0.1.0", ["rt_shared"])
])
expect(error).to_contain("duplicate extern symbol")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/plugin/manifest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Plugin manifest registry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
