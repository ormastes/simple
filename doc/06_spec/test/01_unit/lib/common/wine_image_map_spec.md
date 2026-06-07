# Wine Image Map Specification

> <details>

<!-- sdn-diagram:id=wine_image_map_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_image_map_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_image_map_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_image_map_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Image Map Specification

## Scenarios

### Wine image map gate

#### requires an entry point

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_image_map_gate(_minimal_image(0, 0x5000))).to_equal("missing-entrypoint")
```

</details>

#### requires the entry point to map through a section

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_image_map_gate(_minimal_image(0x9000, 0x5000))).to_equal("entrypoint-unmapped")
```

</details>

#### requires an image larger than headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_image_map_gate(_minimal_image(0x2010, 0x100))).to_equal("bad-image-size")
```

</details>

#### rejects section raw data outside the PE bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_image_map_gate(_minimal_image_with_raw_overflow(0x2010, 0x5000))).to_equal("section-raw-out-of-bounds")
```

</details>

#### requires the entry point section to be executable

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_image_map_gate(_minimal_image_without_executable_section(0x2010, 0x5000))).to_equal("entry-section-not-executable")
```

</details>

#### accepts a bounded mapped image layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_image_map_gate(_minimal_image(0x2010, 0x5000))).to_equal("ready")
```

</details>

#### requires the entry execution window to stay mapped and contiguous

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_image_entry_window_gate(_minimal_image(0x2010, 0x5000), 27)).to_equal("ready")
expect(wine_image_entry_window_gate(_minimal_image(0x2010, 0x5000), 0)).to_equal("invalid-entry-window")
expect(wine_image_entry_window_gate(_minimal_image(0x21f0, 0x5000), 32)).to_equal("entry-window-unmapped")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_image_map_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine image map gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
