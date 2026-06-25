# Tolerance Profile Specification

> <details>

<!-- sdn-diagram:id=tolerance_profile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tolerance_profile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tolerance_profile_spec -> std
tolerance_profile_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tolerance_profile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tolerance Profile Specification

## Scenarios

### ToleranceProfile — preset profiles

#### strict profile

#### AC-4: strict profile has zero default threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = profile_strict()
expect(p.default_threshold).to_equal(0)
```

</details>

#### AC-4: strict profile has zero yiq threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = profile_strict()
expect(p.default_yiq_threshold).to_equal(0.0)
```

</details>

#### AC-4: strict profile has name 'strict'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = profile_strict()
expect(p.name).to_equal("strict")
```

</details>

#### text-tolerant profile

#### AC-4: text tolerant profile has nonzero threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = profile_text_tolerant()
expect(p.default_threshold).to_be_greater_than(0)
```

</details>

#### AC-4: text tolerant profile has positive yiq threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = profile_text_tolerant()
expect(p.default_yiq_threshold).to_be_greater_than(0.0)
```

</details>

#### AC-4: text tolerant profile has name 'text_tolerant'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = profile_text_tolerant()
expect(p.name).to_equal("text_tolerant")
```

</details>

#### AC-4: text tolerant profile includes text region tolerance

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = profile_text_tolerant()
val has_text_region = p.regions.len() > 0
expect(has_text_region).to_equal(true)
```

</details>

#### glass blur profile

#### AC-4: glass blur profile has threshold >= 12

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = profile_glass_blur()
val above_12 = p.default_threshold >= 12
expect(above_12).to_equal(true)
```

</details>

#### AC-4: glass blur profile has name 'glass_blur'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = profile_glass_blur()
expect(p.name).to_equal("glass_blur")
```

</details>

#### WM default profile

#### AC-4: wm default profile exists and has a name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = profile_wm_default()
expect(p.name).to_equal("wm_default")
```

</details>

#### AC-4: wm default profile has multiple region tolerances

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = profile_wm_default()
val has_regions = p.regions.len() > 1
expect(has_regions).to_equal(true)
```

</details>

#### AC-4: wm default profile has nonzero default threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = profile_wm_default()
expect(p.default_threshold).to_be_greater_than(0)
```

</details>

#### pixel acceptance policy

#### hardening policy disables tolerant acceptance by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gui_pixel_policy_allows_tolerance()).to_equal(false)
```

</details>

#### strict profile is accepted by policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = profile_strict()
expect(tolerance_profile_is_strict(p)).to_equal(true)
expect(tolerance_profile_is_quarantined(p)).to_equal(false)
expect(tolerance_profile_allows_acceptance(p)).to_equal(true)
```

</details>

#### tolerant profiles are quarantined by policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = profile_text_tolerant()
expect(tolerance_profile_is_strict(p)).to_equal(false)
expect(tolerance_profile_is_quarantined(p)).to_equal(true)
expect(tolerance_profile_allows_acceptance(p)).to_equal(false)
```

</details>

### ToleranceProfile — region tolerances

#### RegionTolerance structure

#### AC-4: region tolerance has region_type field

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = profile_wm_default()
val first = p.regions[0]
val has_type = first.region_type.len() > 0
expect(has_type).to_equal(true)
```

</details>

#### AC-4: region tolerance has non-negative threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = profile_wm_default()
val first = p.regions[0]
val non_neg = first.threshold >= 0
expect(non_neg).to_equal(true)
```

</details>

#### AC-4: region tolerance has min_match_pct between 0 and 10000

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = profile_wm_default()
val first = p.regions[0]
val in_range = first.min_match_pct >= 0 and first.min_match_pct <= 10000
expect(in_range).to_equal(true)
```

</details>

### ToleranceProfile — merge_profiles

#### merging two profiles

#### AC-4: merged profile takes overlay name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = profile_strict()
val overlay = profile_text_tolerant()
val merged = merge_profiles(base, overlay)
expect(merged.name).to_equal("text_tolerant")
```

</details>

#### AC-4: merged profile has overlay default_threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = profile_strict()
val overlay = profile_glass_blur()
val merged = merge_profiles(base, overlay)
expect(merged.default_threshold).to_equal(overlay.default_threshold)
```

</details>

#### AC-4: merged profile contains regions from both profiles

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = profile_text_tolerant()
val overlay = profile_glass_blur()
val merged = merge_profiles(base, overlay)
val combined_len = base.regions.len() + overlay.regions.len()
val has_all = merged.regions.len() >= base.regions.len()
expect(has_all).to_equal(true)
```

</details>

#### merging with strict (identity-like)

#### AC-4: merging strict with itself yields strict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = profile_strict()
val merged = merge_profiles(base, base)
expect(merged.default_threshold).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/tolerance_profile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ToleranceProfile — preset profiles
- ToleranceProfile — region tolerances
- ToleranceProfile — merge_profiles

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
