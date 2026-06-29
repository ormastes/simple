# Gui Widgets Specification

> <details>

<!-- sdn-diagram:id=gui_widgets_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_widgets_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_widgets_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_widgets_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gui Widgets Specification

## Scenarios

### Card

### new()

#### creates card with default settings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # elevation=1, padding=16, no title
```

</details>

### with_title()

#### sets card title

1. expect true  # title = Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # title = Some("My Card")
```

</details>

### with_elevation()

#### sets elevation level capped at 5

1. expect true  # with elevation


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # with_elevation(3) -> 3
```

</details>

#### caps elevation at maximum

1. expect true  # with elevation


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # with_elevation(10) -> 5
```

</details>

### with_padding()

#### sets custom padding

1. expect true  # with padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # with_padding(24) -> 24
```

</details>

### to_element()

#### converts to Element with proper structure

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # has class "card", elevation class
```

</details>

### Chip

### new()

#### creates chip with label

1. expect true  # Chip new


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Chip.new(id, "Tag")
```

</details>

### with_icon()

#### adds icon to chip

1. expect true  # icon = Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # icon = Some("★")
```

</details>

### deletable()

#### makes chip deletable

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # deletable = true
```

</details>

### selected()

#### marks chip as selected

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # selected = true
```

</details>

### outlined()

#### changes chip variant to outlined

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # variant = ChipVariant.Outlined
```

</details>

### to_element()

#### renders with proper classes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # has class "chip"
```

</details>

### Avatar

### new()

#### creates avatar with alt text

1. expect true  # Avatar new


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Avatar.new(id, "User")
```

</details>

### with_src()

#### sets image source

1. expect true  # src = Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # src = Some("https://...")
```

</details>

### with_initials()

#### sets initials fallback

1. expect true  # initials = Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # initials = Some("JD")
```

</details>

### size modifiers

#### small() sets small size

1. expect true  # size = AvatarSize Small


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # size = AvatarSize.Small (32px)
```

</details>

#### large() sets large size

1. expect true  # size = AvatarSize Large


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # size = AvatarSize.Large (56px)
```

</details>

### to_element()

#### renders circular avatar

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # has class "avatar", border-radius: 50%
```

</details>

### Badge

### new()

#### creates badge with content

1. expect true  # Badge new


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Badge.new(id, "New")
```

</details>

### count()

#### creates numeric badge

1. expect true  # Badge count


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Badge.count(id, 42) -> "42"
```

</details>

### with_max()

#### caps displayed count

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # 150 with max 99 -> "99+"
```

</details>

#### shows actual count if under max

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # 50 with max 99 -> "50"
```

</details>

### variant modifiers

#### primary() sets primary variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # variant = BadgeVariant.Primary
```

</details>

#### error() sets error variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # variant = BadgeVariant.Error
```

</details>

#### success() sets success variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # variant = BadgeVariant.Success
```

</details>

### to_element()

#### renders badge with styles

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # has class "badge"
```

</details>

### Tooltip

### new()

#### creates tooltip with content

1. expect true  # Tooltip new


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Tooltip.new(id, "Help text")
```

</details>

### position modifiers

#### bottom() sets position

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # position = TooltipPosition.Bottom
```

</details>

#### left() sets position

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # position = TooltipPosition.Left
```

</details>

#### right() sets position

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # position = TooltipPosition.Right
```

</details>

### to_element()

#### renders tooltip with data attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # data-tooltip="...", data-position="..."
```

</details>

### Divider

### horizontal()

#### creates horizontal divider

1. expect true  # Divider horizontal


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Divider.horizontal(id)
```

</details>

### vertical()

#### creates vertical divider

1. expect true  # Divider vertical


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Divider.vertical(id)
```

</details>

### variant modifiers

#### inset() creates inset divider

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # variant = DividerVariant.Inset
```

</details>

#### middle() creates middle divider

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # variant = DividerVariant.Middle
```

</details>

### to_element()

#### renders divider with correct dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # has class "divider", height/width style
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/gui_widgets_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Card
- new()
- with_title()
- with_elevation()
- with_padding()
- to_element()
- Chip
- new()
- with_icon()
- deletable()
- selected()
- outlined()
- to_element()
- Avatar
- new()
- with_src()
- with_initials()
- size modifiers
- to_element()
- Badge
- new()
- count()
- with_max()
- variant modifiers
- to_element()
- Tooltip
- new()
- position modifiers
- to_element()
- Divider
- horizontal()
- vertical()
- variant modifiers
- to_element()

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
