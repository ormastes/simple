# Gui Widgets Specification

> Tests covering Card, new(), with_title(), with_elevation(), with_padding(), to_element(), Chip, new(), with_icon(), deletable(), selected(), outlined(), to_element(), Avatar, new(), with_src(), with_initials(), size modifiers, to_element(), Badge, new(), count(), with_max(), variant modifiers, to_element(), Tooltip, new(), position modifiers, to_element(), Divider, horizontal(), vertical(), variant modifiers, to_element().

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

- creates card with default settings


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates card with default settings")
expect true  # elevation=1, padding=16, no title
```

</details>

### with_title()

#### sets card title

- sets card title


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets card title")
expect true  # title = Some("My Card")
```

</details>

### with_elevation()

#### sets elevation level capped at 5

- sets elevation level capped at 5


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets elevation level capped at 5")
expect true  # with_elevation(3) -> 3
```

</details>

#### caps elevation at maximum

- caps elevation at maximum


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caps elevation at maximum")
expect true  # with_elevation(10) -> 5
```

</details>

### with_padding()

#### sets custom padding

- sets custom padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets custom padding")
expect true  # with_padding(24) -> 24
```

</details>

### to_element()

#### converts to Element with proper structure

- converts to Element with proper structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to Element with proper structure")
expect true  # has class "card", elevation class
```

</details>

### Chip

### new()

#### creates chip with label

- creates chip with label


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates chip with label")
expect true  # Chip.new(id, "Tag")
```

</details>

### with_icon()

#### adds icon to chip

- adds icon to chip


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds icon to chip")
expect true  # icon = Some("★")
```

</details>

### deletable()

#### makes chip deletable

- makes chip deletable


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("makes chip deletable")
expect true  # deletable = true
```

</details>

### selected()

#### marks chip as selected

- marks chip as selected


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks chip as selected")
expect true  # selected = true
```

</details>

### outlined()

#### changes chip variant to outlined

- changes chip variant to outlined


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("changes chip variant to outlined")
expect true  # variant = ChipVariant.Outlined
```

</details>

### to_element()

#### renders with proper classes

- renders with proper classes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders with proper classes")
expect true  # has class "chip"
```

</details>

### Avatar

### new()

#### creates avatar with alt text

- creates avatar with alt text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates avatar with alt text")
expect true  # Avatar.new(id, "User")
```

</details>

### with_src()

#### sets image source

- sets image source


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets image source")
expect true  # src = Some("https://...")
```

</details>

### with_initials()

#### sets initials fallback

- sets initials fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets initials fallback")
expect true  # initials = Some("JD")
```

</details>

### size modifiers

#### small() sets small size

- small() sets small size


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("small() sets small size")
expect true  # size = AvatarSize.Small (32px)
```

</details>

#### large() sets large size

- large() sets large size


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("large() sets large size")
expect true  # size = AvatarSize.Large (56px)
```

</details>

### to_element()

#### renders circular avatar

- renders circular avatar


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders circular avatar")
expect true  # has class "avatar", border-radius: 50%
```

</details>

### Badge

### new()

#### creates badge with content

- creates badge with content


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates badge with content")
expect true  # Badge.new(id, "New")
```

</details>

### count()

#### creates numeric badge

- creates numeric badge


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates numeric badge")
expect true  # Badge.count(id, 42) -> "42"
```

</details>

### with_max()

#### caps displayed count

- caps displayed count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caps displayed count")
expect true  # 150 with max 99 -> "99+"
```

</details>

#### shows actual count if under max

- shows actual count if under max


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows actual count if under max")
expect true  # 50 with max 99 -> "50"
```

</details>

### variant modifiers

#### primary() sets primary variant

- primary() sets primary variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("primary() sets primary variant")
expect true  # variant = BadgeVariant.Primary
```

</details>

#### error() sets error variant

- error() sets error variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error() sets error variant")
expect true  # variant = BadgeVariant.Error
```

</details>

#### success() sets success variant

- success() sets success variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("success() sets success variant")
expect true  # variant = BadgeVariant.Success
```

</details>

### to_element()

#### renders badge with styles

- renders badge with styles


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders badge with styles")
expect true  # has class "badge"
```

</details>

### Tooltip

### new()

#### creates tooltip with content

- creates tooltip with content


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates tooltip with content")
expect true  # Tooltip.new(id, "Help text")
```

</details>

### position modifiers

#### bottom() sets position

- bottom() sets position


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bottom() sets position")
expect true  # position = TooltipPosition.Bottom
```

</details>

#### left() sets position

- left() sets position


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("left() sets position")
expect true  # position = TooltipPosition.Left
```

</details>

#### right() sets position

- right() sets position


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("right() sets position")
expect true  # position = TooltipPosition.Right
```

</details>

### to_element()

#### renders tooltip with data attributes

- renders tooltip with data attributes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders tooltip with data attributes")
expect true  # data-tooltip="...", data-position="..."
```

</details>

### Divider

### horizontal()

#### creates horizontal divider

- creates horizontal divider


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates horizontal divider")
expect true  # Divider.horizontal(id)
```

</details>

### vertical()

#### creates vertical divider

- creates vertical divider


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates vertical divider")
expect true  # Divider.vertical(id)
```

</details>

### variant modifiers

#### inset() creates inset divider

- inset() creates inset divider


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inset() creates inset divider")
expect true  # variant = DividerVariant.Inset
```

</details>

#### middle() creates middle divider

- middle() creates middle divider


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("middle() creates middle divider")
expect true  # variant = DividerVariant.Middle
```

</details>

### to_element()

#### renders divider with correct dimensions

- renders divider with correct dimensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders divider with correct dimensions")
expect true  # has class "divider", height/width style
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/gui_widgets_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Card, new(), with_title(), with_elevation(), with_padding(), to_element(), Chip, new(), with_icon(), deletable(), selected(), outlined(), to_element(), Avatar, new(), with_src(), with_initials(), size modifiers, to_element(), Badge, new(), count(), with_max(), variant modifiers, to_element(), Tooltip, new(), position modifiers, to_element(), Divider, horizontal(), vertical(), variant modifiers, to_element().
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `927cc8a78a08858e6ad3eda283de3398af211f5a3fbcdabb74d152ad19e0cc9c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `927cc8a78a08858e6ad3eda283de3398af211f5a3fbcdabb74d152ad19e0cc9c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `927cc8a78a08858e6ad3eda283de3398af211f5a3fbcdabb74d152ad19e0cc9c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/gui_widgets_spec.spl
mirror: doc/06_spec/unit/app/ui/gui_widgets_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/gui_widgets_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/gui_widgets_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/gui_widgets_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates card with default settings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/gui_widgets_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets card title' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/gui_widgets_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets elevation level capped at 5' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
