# UI UIColor Codec Specification

> Round-trip tests for `UIColor.from_hex()` / `to_hex()` codec. Verifies byte-identical round-trips for every hex literal that appears in the iOS and Glass theme files, plus style.spl dark/light constants.

<!-- sdn-diagram:id=color_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=color_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

color_spec -> std
color_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=color_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 50 | 50 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UI UIColor Codec Specification

Round-trip tests for `UIColor.from_hex()` / `to_hex()` codec. Verifies byte-identical round-trips for every hex literal that appears in the iOS and Glass theme files, plus style.spl dark/light constants.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Stdlib |
| Difficulty | 1/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/05_design/ui_typed_core_rfc.md |
| Source | `test/01_unit/app/ui/color_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Round-trip tests for `UIColor.from_hex()` / `to_hex()` codec.
Verifies byte-identical round-trips for every hex literal that appears
in the iOS and Glass theme files, plus style.spl dark/light constants.

Case preservation: from_hex("#1e1e2e").to_hex() == "#1e1e2e" (lowercase
preserved); from_hex("#007AFF").to_hex() == "#007AFF" (uppercase preserved).

Wire stability: rgba() strings with decimal alpha are intentionally
NOT tested here — they cannot be represented as UIColor (u8 alpha is lossy).

## Scenarios

### UIColor.from_hex — basic parsing

#### parses 6-digit uppercase hex components

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = UIColor.from_hex("#007AFF")
expect(c.r).to_equal(0)
expect(c.g).to_equal(122)
expect(c.b).to_equal(255)
expect(c.a).to_equal(255)
```

</details>

#### parses 6-digit lowercase hex components

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = UIColor.from_hex("#1e1e2e")
expect(c.r).to_equal(30)
expect(c.g).to_equal(30)
expect(c.b).to_equal(46)
expect(c.a).to_equal(255)
```

</details>

#### parses 8-digit hex with alpha channel

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = UIColor.from_hex("#007AFF80")
expect(c.r).to_equal(0)
expect(c.g).to_equal(122)
expect(c.b).to_equal(255)
expect(c.a).to_equal(128)
```

</details>

#### returns black/opaque for unrecognised format

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = UIColor.from_hex("notahex")
expect(c.r).to_equal(0)
expect(c.g).to_equal(0)
expect(c.b).to_equal(0)
expect(c.a).to_equal(255)
```

</details>

### UIColor.to_hex — output format

#### emits 6-char hex with # prefix when alpha is 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = UIColor(r: 10, g: 132, b: 255, a: 255, case_lower: false)
expect(c.to_hex()).to_equal("#0A84FF")
```

</details>

#### emits 8-char hex with # prefix when alpha is not 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = UIColor(r: 0, g: 0, b: 0, a: 128, case_lower: false)
expect(c.to_hex()).to_equal("#00000080")
```

</details>

#### emits leading zero for single-nibble values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = UIColor(r: 0, g: 10, b: 15, a: 255, case_lower: false)
expect(c.to_hex()).to_equal("#000A0F")
```

</details>

#### emits lowercase a-f when case_lower is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = UIColor(r: 171, g: 205, b: 239, a: 255, case_lower: true)
expect(c.to_hex()).to_equal("#abcdef")
```

</details>

#### emits uppercase A-F when case_lower is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = UIColor(r: 171, g: 205, b: 239, a: 255, case_lower: false)
expect(c.to_hex()).to_equal("#ABCDEF")
```

</details>

### UIColor — case preservation

#### preserves uppercase case through round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#007AFF"
val c = UIColor.from_hex(orig)
expect(c.to_hex()).to_equal(orig)
```

</details>

#### preserves lowercase case through round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#1e1e2e"
val c = UIColor.from_hex(orig)
expect(c.to_hex()).to_equal(orig)
```

</details>

#### preserves uppercase when all digits are 0-9 (no letter ambiguity)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#F0F0F5"
val c = UIColor.from_hex(orig)
expect(c.to_hex()).to_equal(orig)
```

</details>

### UIColor round-trip — style.spl dark() constants

#### round-trips #1e1e2e (background)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#1e1e2e"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #cdd6f4 (foreground)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#cdd6f4"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #45475a (border/hover_bg)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#45475a"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #89b4fa (accent/info)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#89b4fa"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #313244 (panel_bg)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#313244"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #f38ba8 (error)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#f38ba8"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #fab387 (warning)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#fab387"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #a6e3a1 (success)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#a6e3a1"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

### UIColor round-trip — style.spl light() constants

#### round-trips #ffffff (background)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#ffffff"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #333333 (foreground)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#333333"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #0066cc (accent)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#0066cc"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #dc3545 (error)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#dc3545"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #28a745 (success)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#28a745"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #17a2b8 (info)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#17a2b8"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

### UIColor round-trip — iOS theme constants

#### round-trips #F2F2F7 (ios_light background)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#F2F2F7"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #000000 (ios_light foreground)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#000000"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #007AFF (ios_light accent)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#007AFF"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #FF3B30 (ios_light error)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#FF3B30"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #FF9500 (ios_light warning)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#FF9500"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #34C759 (ios_light success)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#34C759"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #5AC8FA (ios_light info)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#5AC8FA"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #0A84FF (ios_dark accent)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#0A84FF"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #FFFFFF (ios_dark foreground)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#FFFFFF"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #1C1C1E (ios_dark panel_bg hex)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#1C1C1E"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #FF453A (ios_dark error)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#FF453A"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #FF9F0A (ios_dark warning)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#FF9F0A"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #30D158 (ios_dark success)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#30D158"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #64D2FF (ios_dark info)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#64D2FF"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

### UIColor round-trip — Glass theme hex constants

#### round-trips #F0F0F5 (glass_light background)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#F0F0F5"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #1D1D1F (glass_light/obsidian_light foreground)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#1D1D1F"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #0A0A0F (glass_dark background)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#0A0A0F"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #F5F5F7 (glass_dark foreground)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#F5F5F7"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #060612 (glass_obsidian_dark background)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#060612"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #E3E0F3 (glass_obsidian_dark foreground)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#E3E0F3"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #C6C6C8 (glass_obsidian_dark accent)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#C6C6C8"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #FFB4AB (glass_obsidian_dark error)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#FFB4AB"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #F0ECF5 (glass_obsidian_light background)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#F0ECF5"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

#### round-trips #7C69A3 (glass_obsidian_light accent)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = "#7C69A3"
expect(UIColor.from_hex(orig).to_hex()).to_equal(orig)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 50 |
| Active scenarios | 50 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/05_design/ui_typed_core_rfc.md](doc/05_design/ui_typed_core_rfc.md)


</details>
