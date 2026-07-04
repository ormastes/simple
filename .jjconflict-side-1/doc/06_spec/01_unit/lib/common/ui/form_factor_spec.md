# Form Factor Specification

> <details>

<!-- sdn-diagram:id=form_factor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=form_factor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

form_factor_spec -> std
form_factor_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=form_factor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Form Factor Specification

## Scenarios

### detect_device_class

#### macos no-touch wide → Desktop

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_device_class("macos", false, 900)).to_equal(DeviceClass.Desktop)
```

</details>

#### android touch narrow → Phone

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_device_class("android", true, 411)).to_equal(DeviceClass.Phone)
```

</details>

#### android touch 600 → Tablet (boundary: >=600 Tablet)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_device_class("android", true, 600)).to_equal(DeviceClass.Tablet)
```

</details>

#### ios touch 599 → Phone

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_device_class("ios", true, 599)).to_equal(DeviceClass.Phone)
```

</details>

#### ipados touch 768 → Tablet

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_device_class("ipados", true, 768)).to_equal(DeviceClass.Tablet)
```

</details>

#### empty platform no-touch 500 → Desktop (unknown+no-touch)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_device_class("", false, 500)).to_equal(DeviceClass.Desktop)
```

</details>

#### windows touch 1000 → Tablet (touch-first windows tablet)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_device_class("windows", true, 1000)).to_equal(DeviceClass.Tablet)
```

</details>

### DeviceClass.to_wire

#### Phone → phone

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DeviceClass.Phone.to_wire()).to_equal("phone")
```

</details>

#### Tablet → tablet

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DeviceClass.Tablet.to_wire()).to_equal("tablet")
```

</details>

#### Desktop → desktop

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DeviceClass.Desktop.to_wire()).to_equal("desktop")
```

</details>

### compute_form_factor

#### 390x844 ios touch → Phone, horizontal Compact, Portrait

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vp = new_viewport(390, 844, "gui")
val ff = compute_form_factor(vp, "ios", true)
expect(ff.device).to_equal(DeviceClass.Phone)
expect(ff.layout.horizontal).to_equal(SizeClass.Compact)
expect(ff.layout.orientation).to_equal(Orientation.Portrait)
```

</details>

#### 1024x768 ipados touch → Tablet, horizontal Expanded

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vp = new_viewport(1024, 768, "gui")
val ff = compute_form_factor(vp, "ipados", true)
expect(ff.device).to_equal(DeviceClass.Tablet)
expect(ff.layout.horizontal).to_equal(SizeClass.Expanded)
```

</details>

#### 1440x900 macos no-touch → Desktop, horizontal Expanded

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vp = new_viewport(1440, 900, "gui")
val ff = compute_form_factor(vp, "macos", false)
expect(ff.device).to_equal(DeviceClass.Desktop)
expect(ff.layout.horizontal).to_equal(SizeClass.Expanded)
```

</details>

#### 844x390 ios touch landscape phone → Phone, vertical Compact

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vp = new_viewport(844, 390, "gui")
val ff = compute_form_factor(vp, "ios", true)
expect(ff.device).to_equal(DeviceClass.Phone)
expect(ff.layout.vertical).to_equal(SizeClass.Compact)
```

</details>

### default_breakpoints width boundaries

#### classify(599) = Compact

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = default_breakpoints()
expect(classify(599, bp)).to_equal(SizeClass.Compact)
```

</details>

#### classify(600) = Regular

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = default_breakpoints()
expect(classify(600, bp)).to_equal(SizeClass.Regular)
```

</details>

#### classify(839) = Regular

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = default_breakpoints()
expect(classify(839, bp)).to_equal(SizeClass.Regular)
```

</details>

#### classify(840) = Expanded

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = default_breakpoints()
expect(classify(840, bp)).to_equal(SizeClass.Expanded)
```

</details>

### height_breakpoints boundaries

#### classify(479) = Compact

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = height_breakpoints()
expect(classify(479, bp)).to_equal(SizeClass.Compact)
```

</details>

#### classify(480) = Regular

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = height_breakpoints()
expect(classify(480, bp)).to_equal(SizeClass.Regular)
```

</details>

#### classify(899) = Regular

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = height_breakpoints()
expect(classify(899, bp)).to_equal(SizeClass.Regular)
```

</details>

#### classify(900) = Expanded

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = height_breakpoints()
expect(classify(900, bp)).to_equal(SizeClass.Expanded)
```

</details>

### min_touch_target

#### Phone ios → 44

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(min_touch_target(DeviceClass.Phone, "ios")).to_equal(44)
```

</details>

#### Phone android → 48

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(min_touch_target(DeviceClass.Phone, "android")).to_equal(48)
```

</details>

#### Tablet ipados → 44

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(min_touch_target(DeviceClass.Tablet, "ipados")).to_equal(44)
```

</details>

#### Desktop macos → 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(min_touch_target(DeviceClass.Desktop, "macos")).to_equal(32)
```

</details>

### supports_hover

#### Desktop → true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(supports_hover(DeviceClass.Desktop)).to_equal(true)
```

</details>

#### Phone → false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(supports_hover(DeviceClass.Phone)).to_equal(false)
```

</details>

#### Tablet → false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(supports_hover(DeviceClass.Tablet)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/form_factor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- detect_device_class
- DeviceClass.to_wire
- compute_form_factor
- default_breakpoints width boundaries
- height_breakpoints boundaries
- min_touch_target
- supports_hover

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
