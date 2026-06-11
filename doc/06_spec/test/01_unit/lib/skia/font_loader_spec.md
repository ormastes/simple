# Skia Font Loader Specification

> Tests for FontRegistry — the in-memory stub backing SkFontMgr-style family enumeration and matchFamilyStyle lookup.

<!-- sdn-diagram:id=font_loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=font_loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

font_loader_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=font_loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Font Loader Specification

Tests for FontRegistry — the in-memory stub backing SkFontMgr-style family enumeration and matchFamilyStyle lookup.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-FONT-LOADER |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/font_loader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for FontRegistry — the in-memory stub backing SkFontMgr-style family
enumeration and matchFamilyStyle lookup.

## Scenarios

### font_loader

#### font_registry_new: empty registry has zero families

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = font_registry_new()
expect(reg.family_count()).to_equal(0)
expect(reg.list_families().length()).to_equal(0)
```

</details>

#### register + list_families: returns added family names

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = font_registry_new()
val style = FontStyle(weight: FontWeight.Regular, slant: FontSlant.Upright)
reg.register(FontFamilyEntry(
    family: "Alpha",
    style: style,
    typeface_name: "",
    path: ""
))
reg.register(FontFamilyEntry(
    family: "Beta",
    style: style,
    typeface_name: "",
    path: ""
))
val families = reg.list_families()
expect(families.length()).to_equal(2)
expect(families[0]).to_equal("Alpha")
expect(families[1]).to_equal("Beta")
expect(reg.family_count()).to_equal(2)
```

</details>

#### default_font_registry: has Sans, Serif, Monospace

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = default_font_registry()
expect(reg.family_count()).to_equal(3)
val families = reg.list_families()
expect(families[0]).to_equal("Sans")
expect(families[1]).to_equal("Serif")
expect(families[2]).to_equal("Monospace")
```

</details>

#### match_family_style: exact match returns Some

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = default_font_registry()
val style = FontStyle(weight: FontWeight.Regular, slant: FontSlant.Upright)
val result = reg.match_family_style("Serif", style)
val entry = result.unwrap()
expect(entry.family).to_equal("Serif")
```

</details>

#### match_family_style: unknown family returns None

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = default_font_registry()
val style = FontStyle(weight: FontWeight.Regular, slant: FontSlant.Upright)
val result = reg.match_family_style("Nonexistent", style)
expect(result).to_be_nil()
```

</details>

#### match_family_style: fallback to closest weight when exact weight missing

1. style: FontStyle
2. style: FontStyle
   - Expected: entry.family equals `Custom`
   - Expected: is_black is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = font_registry_new()
# Register only Thin (100) and Black (900) upright variants.
reg.register(FontFamilyEntry(
    family: "Custom",
    style: FontStyle(weight: FontWeight.Thin, slant: FontSlant.Upright),
    typeface_name: "",
    path: ""
))
reg.register(FontFamilyEntry(
    family: "Custom",
    style: FontStyle(weight: FontWeight.Black, slant: FontSlant.Upright),
    typeface_name: "",
    path: ""
))
# Request Medium (500) — closer to Black (900, dist 400) than Thin (100, dist 400)?
# Thin dist = |500 - 100| = 400; Black dist = |500 - 900| = 400. Tie — first wins (Thin).
# Use Bold (700) instead: Thin dist 600, Black dist 200 -> Black wins.
val style = FontStyle(weight: FontWeight.Bold, slant: FontSlant.Upright)
val result = reg.match_family_style("Custom", style)
val entry = result.unwrap()
expect(entry.family).to_equal("Custom")
val is_black = entry.style.weight == FontWeight.Black
expect(is_black).to_equal(true)
expect(reg.family_count()).to_be_greater_than(0)
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


</details>
