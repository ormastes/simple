# Text Presence Functions Specification

> Tests `presence` and `presence_trimmed` functions that convert text to `text?`, returning the value if non-empty/non-blank, or `nil` otherwise.

<!-- sdn-diagram:id=text_empty_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=text_empty_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

text_empty_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=text_empty_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Presence Functions Specification

Tests `presence` and `presence_trimmed` functions that convert text to `text?`, returning the value if non-empty/non-blank, or `nil` otherwise.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2100-PRESENCE |
| Category | Stdlib |
| Difficulty | 1/5 |
| Status | Implemented |
| Research | doc/01_research/text_validity_presence_pattern_2026-02-24.md |
| Source | `test/01_unit/lib/common/text_empty_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests `presence` and `presence_trimmed` functions that convert text to `text?`,
returning the value if non-empty/non-blank, or `nil` otherwise.

## Note

Functions are defined locally because importing `lib.common.text` causes
timeout (~40s) due to heavy transitive dependencies. The canonical source
is `src/lib/common/text.spl`. These local copies mirror that implementation.

## Scenarios

### presence

#### returns value for non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(presence("hello") ?? "").to_equal("hello")
```

</details>

#### returns nil for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(presence("") ?? "default").to_equal("default")
```

</details>

#### returns whitespace string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(presence("  ") ?? "").to_equal("  ")
```

</details>

### presence_trimmed

#### returns value for non-blank

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(presence_trimmed("hello") ?? "").to_equal("hello")
```

</details>

#### returns nil for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(presence_trimmed("") ?? "default").to_equal("default")
```

</details>

#### returns nil for whitespace-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(presence_trimmed("  ") ?? "default").to_equal("default")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** [doc/01_research/text_validity_presence_pattern_2026-02-24.md](doc/01_research/text_validity_presence_pattern_2026-02-24.md)


</details>
