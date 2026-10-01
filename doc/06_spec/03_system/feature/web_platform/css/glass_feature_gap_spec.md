# Glass Feature Gap Specification

> <details>

<!-- sdn-diagram:id=glass_feature_gap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=glass_feature_gap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

glass_feature_gap_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=glass_feature_gap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glass Feature Gap Specification

## Scenarios

### Glass comparison feature gap detection

#### does not report supported before and after pseudo-elements as missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<style>.card::before { content: 'A'; } .card::after { content: 'B'; }</style><div class='card'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "pseudo-elements (::before/::after)")).to_equal(false)
```

</details>

#### still reports unsupported glass effect features

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<style>.panel { backdrop-filter: blur(12px); box-shadow: 0 8px 24px #000; }</style><div class='panel'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "backdrop-filter: blur()")).to_equal(true)
expect(_contains(missing, "box-shadow (multi-layer)")).to_equal(false)
```

</details>

#### does not report multi-layer box shadow as unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<style>.panel { box-shadow: 0 8px 24px #000, 0 2px 6px #333; }</style><div class='panel'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "box-shadow (multi-layer)")).to_equal(false)
```

</details>

#### does not report linear gradients as unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<style>.panel { background: linear-gradient(180deg, #fff, #000); }</style><div class='panel'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "linear-gradient()")).to_equal(false)
```

</details>

#### does not report simple translate transforms as unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<style>.panel { transform: translate(4px, 4px); }</style><div class='panel'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "transform")).to_equal(false)
```

</details>

#### still reports unsupported transform functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<style>.panel { transform: rotate(5deg); }</style><div class='panel'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "transform")).to_equal(true)
```

</details>

#### still reports multi-function translate transforms as partial

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<style>.panel { transform: translate(4px, 4px) translateX(2px); }</style><div class='panel'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "transform")).to_equal(true)
```

</details>

#### does not report simple percentage translate transforms as unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<style>.panel { transform: translate(50%, 0); }</style><div class='panel'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "transform")).to_equal(false)
```

</details>

#### still reports translate transforms with unsupported units

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<style>.panel { transform: translate(2em, 0); }</style><div class='panel'></div>"
val missing = identify_missing_features(html)
expect(_contains(missing, "transform")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/glass_feature_gap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Glass comparison feature gap detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
