# Location Api Specification

> <details>

<!-- sdn-diagram:id=location_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=location_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

location_api_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=location_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Location Api Specification

## Scenarios

### Browser script location API

### Location

#### parses URL fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = location_from_url("https://example.test/path/page?q=1#top")
expect(loc.href).to_equal("https://example.test/path/page?q=1#top")
expect(loc.protocol).to_equal("https:")
expect(loc.host).to_equal("example.test")
expect(loc.pathname).to_equal("/path/page")
expect(loc.search).to_equal("?q=1")
expect(loc.hash).to_equal("#top")
```

</details>

#### parses search without hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = location_from_url("http://other.test/next?q=2")
expect(loc.protocol).to_equal("http:")
expect(loc.host).to_equal("other.test")
expect(loc.pathname).to_equal("/next")
expect(loc.search).to_equal("?q=2")
expect(loc.hash).to_equal("")
```

</details>

#### assigns a new location

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = location_from_url("https://example.test/start")
val next = location_assign(loc, "http://other.test/next?q=2")
expect(next.href).to_equal("http://other.test/next?q=2")
expect(next.protocol).to_equal("http:")
expect(next.host).to_equal("other.test")
expect(next.pathname).to_equal("/next")
expect(next.search).to_equal("?q=2")
```

</details>

#### reload refreshes parsed fields from current href

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = location_from_url("https://example.test/start")
loc.href = "https://example.test/reloaded?q=3#done"
val reloaded = location_reload(loc)
expect(reloaded.href).to_equal("https://example.test/reloaded?q=3#done")
expect(reloaded.protocol).to_equal("https:")
expect(reloaded.host).to_equal("example.test")
expect(reloaded.pathname).to_equal("/reloaded")
expect(reloaded.search).to_equal("?q=3")
expect(reloaded.hash).to_equal("#done")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/script/location_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser script location API
- Location

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
