# Token Resolution Specification

> Verifies that typed design-token enums (Spacing, Radius, Elevation, SurfaceRole, TextRole) resolve to the correct raw values through ThemeRegistry resolver methods, and that to_wire() codecs produce stable lowercase canonical strings.

<!-- sdn-diagram:id=token_resolution_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=token_resolution_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

token_resolution_spec -> std
token_resolution_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=token_resolution_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Token Resolution Specification

Verifies that typed design-token enums (Spacing, Radius, Elevation, SurfaceRole, TextRole) resolve to the correct raw values through ThemeRegistry resolver methods, and that to_wire() codecs produce stable lowercase canonical strings.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Design | doc/05_design/ui_typed_core_rfc.md |
| Source | `test/01_unit/app/ui/token_resolution_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that typed design-token enums (Spacing, Radius, Elevation, SurfaceRole,
TextRole) resolve to the correct raw values through ThemeRegistry resolver methods,
and that to_wire() codecs produce stable lowercase canonical strings.

## Key Concepts

| Concept        | Description                                              |
|----------------|----------------------------------------------------------|
| Spacing        | 5-step spacing scale (Xs=4 .. Xl=32)                     |
| Radius         | Border-radius tokens (None=0 .. Pill=999)                |
| Elevation      | Elevation level integers (Flat=0 .. High=8)              |
| SurfaceRole    | Semantic surface color tokens mapped to GlassColorTokens |
| TextRole       | Semantic text color tokens mapped to GlassColorTokens    |
| to_wire()      | Stable lowercase snake_case canonical string per token   |

## Scenarios

### ThemeId canonical key helper

#### maps GlassDark to glass_dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(theme_id_key(ThemeId.GlassDark)).to_equal("glass_dark")
```

</details>

#### preserves custom theme names

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(theme_id_key(ThemeId.Custom("custom_theme"))).to_equal("custom_theme")
```

</details>

### ThemeRegistry resolve_spacing defaults

#### resolves Spacing.Xs to 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val px = r.resolve_spacing(ThemeId.Custom("token_test"), Spacing.Xs)
expect(px).to_equal(4)
```

</details>

#### resolves Spacing.Sm to 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val px = r.resolve_spacing(ThemeId.Custom("token_test"), Spacing.Sm)
expect(px).to_equal(8)
```

</details>

#### resolves Spacing.Md to 16

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val px = r.resolve_spacing(ThemeId.Custom("token_test"), Spacing.Md)
expect(px).to_equal(16)
```

</details>

#### resolves Spacing.Lg to 24

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val px = r.resolve_spacing(ThemeId.Custom("token_test"), Spacing.Lg)
expect(px).to_equal(24)
```

</details>

#### resolves Spacing.Xl to 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val px = r.resolve_spacing(ThemeId.Custom("token_test"), Spacing.Xl)
expect(px).to_equal(32)
```

</details>

### ThemeRegistry resolve_spacing with registered scale

#### uses the registered scale when present

1. r register spacing scale
   - Expected: px equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
r.register_spacing_scale(ThemeId.Custom("scale_override"), [2, 4, 8, 12, 16])
val px = r.resolve_spacing(ThemeId.Custom("scale_override"), Spacing.Md)
expect(px).to_equal(8)
```

</details>

#### does not affect other themes after override

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val px = r.resolve_spacing(ThemeId.Custom("other_theme"), Spacing.Md)
expect(px).to_equal(16)
```

</details>

### ThemeRegistry resolve_radius defaults

#### resolves Radius.Zero to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val px = r.resolve_radius(ThemeId.Custom("token_test"), Radius.Zero)
expect(px).to_equal(0)
```

</details>

#### resolves Radius.Sm to 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val px = r.resolve_radius(ThemeId.Custom("token_test"), Radius.Sm)
expect(px).to_equal(4)
```

</details>

#### resolves Radius.Md to 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val px = r.resolve_radius(ThemeId.Custom("token_test"), Radius.Md)
expect(px).to_equal(8)
```

</details>

#### resolves Radius.Lg to 16

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val px = r.resolve_radius(ThemeId.Custom("token_test"), Radius.Lg)
expect(px).to_equal(16)
```

</details>

#### resolves Radius.Pill to 999

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val px = r.resolve_radius(ThemeId.Custom("token_test"), Radius.Pill)
expect(px).to_equal(999)
```

</details>

### ThemeRegistry resolve_elevation defaults

#### resolves Elevation.Flat to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val px = r.resolve_elevation(ThemeId.Custom("token_test"), Elevation.Flat)
expect(px).to_equal(0)
```

</details>

#### resolves Elevation.Low to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val px = r.resolve_elevation(ThemeId.Custom("token_test"), Elevation.Low)
expect(px).to_equal(1)
```

</details>

#### resolves Elevation.Mid to 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val px = r.resolve_elevation(ThemeId.Custom("token_test"), Elevation.Mid)
expect(px).to_equal(4)
```

</details>

#### resolves Elevation.High to 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val px = r.resolve_elevation(ThemeId.Custom("token_test"), Elevation.High)
expect(px).to_equal(8)
```

</details>

### ThemeRegistry resolve_surface

#### returns fallback for unregistered theme

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val color = r.resolve_surface(ThemeId.Custom("no_such_theme_xyz"), SurfaceRole.Background)
expect(color).to_equal("#000000")
```

</details>

#### returns fallback for unregistered overlay role

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val color = r.resolve_surface(ThemeId.Custom("no_such_theme_xyz"), SurfaceRole.Overlay)
expect(color).to_equal("#000000")
```

</details>

#### resolves SurfaceRole.Surface from GlassDark tokens

1. var r = theme registry
2. r register tokens
   - Expected: color equals `rgba(30,30,35,0.72)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = theme_registry()
r.register_tokens(ThemeId.Custom("test_glass"), GlassDesignTokens.dark())
val color = r.resolve_surface(ThemeId.Custom("test_glass"), SurfaceRole.Surface)
expect(color).to_equal("rgba(30,30,35,0.72)")
```

</details>

#### resolves SurfaceRole.Background from GlassDark tokens

1. var r = theme registry
2. r register tokens
   - Expected: color equals `#0b0d10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = theme_registry()
r.register_tokens(ThemeId.Custom("test_glass"), GlassDesignTokens.dark())
val color = r.resolve_surface(ThemeId.Custom("test_glass"), SurfaceRole.Background)
expect(color).to_equal("#0b0d10")
```

</details>

### ThemeRegistry resolve_text_role

#### returns fallback for unregistered theme

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = theme_registry()
val color = r.resolve_text_role(ThemeId.Custom("no_such_theme_xyz"), TextRole.Primary)
expect(color).to_equal("#000000")
```

</details>

#### resolves TextRole.Primary from GlassDark tokens

1. var r = theme registry
2. r register tokens
   - Expected: color equals `#F5F5F7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = theme_registry()
r.register_tokens(ThemeId.Custom("test_glass_text"), GlassDesignTokens.dark())
val color = r.resolve_text_role(ThemeId.Custom("test_glass_text"), TextRole.Primary)
expect(color).to_equal("#F5F5F7")
```

</details>

#### resolves TextRole.Danger from GlassDark tokens

1. var r = theme registry
2. r register tokens
   - Expected: color equals `#FF453A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = theme_registry()
r.register_tokens(ThemeId.Custom("test_glass_text"), GlassDesignTokens.dark())
val color = r.resolve_text_role(ThemeId.Custom("test_glass_text"), TextRole.Danger)
expect(color).to_equal("#FF453A")
```

</details>

### Spacing to_wire codecs
_Wire strings are frozen: changing them breaks serializers/lints._

#### Spacing.Xs wire is 'xs'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Spacing.Xs.to_wire()).to_equal("xs")
```

</details>

#### Spacing.Sm wire is 'sm'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Spacing.Sm.to_wire()).to_equal("sm")
```

</details>

#### Spacing.Md wire is 'md'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Spacing.Md.to_wire()).to_equal("md")
```

</details>

#### Spacing.Lg wire is 'lg'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Spacing.Lg.to_wire()).to_equal("lg")
```

</details>

#### Spacing.Xl wire is 'xl'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Spacing.Xl.to_wire()).to_equal("xl")
```

</details>

### Radius to_wire codecs

#### Radius.Zero wire is 'zero'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Radius.Zero.to_wire()).to_equal("zero")
```

</details>

#### Radius.Sm wire is 'sm'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Radius.Sm.to_wire()).to_equal("sm")
```

</details>

#### Radius.Md wire is 'md'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Radius.Md.to_wire()).to_equal("md")
```

</details>

#### Radius.Lg wire is 'lg'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Radius.Lg.to_wire()).to_equal("lg")
```

</details>

#### Radius.Pill wire is 'pill'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Radius.Pill.to_wire()).to_equal("pill")
```

</details>

### Elevation to_wire codecs

#### Elevation.Flat wire is 'flat'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Elevation.Flat.to_wire()).to_equal("flat")
```

</details>

#### Elevation.Low wire is 'low'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Elevation.Low.to_wire()).to_equal("low")
```

</details>

#### Elevation.Mid wire is 'mid'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Elevation.Mid.to_wire()).to_equal("mid")
```

</details>

#### Elevation.High wire is 'high'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Elevation.High.to_wire()).to_equal("high")
```

</details>

### SurfaceRole to_wire codecs

#### SurfaceRole.Background wire is 'background'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SurfaceRole.Background.to_wire()).to_equal("background")
```

</details>

#### SurfaceRole.Surface wire is 'surface'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SurfaceRole.Surface.to_wire()).to_equal("surface")
```

</details>

#### SurfaceRole.Card wire is 'card'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SurfaceRole.Card.to_wire()).to_equal("card")
```

</details>

#### SurfaceRole.Overlay wire is 'overlay'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SurfaceRole.Overlay.to_wire()).to_equal("overlay")
```

</details>

### TextRole to_wire codecs

#### TextRole.Primary wire is 'primary'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TextRole.Primary.to_wire()).to_equal("primary")
```

</details>

#### TextRole.Secondary wire is 'secondary'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TextRole.Secondary.to_wire()).to_equal("secondary")
```

</details>

#### TextRole.Muted wire is 'muted'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TextRole.Muted.to_wire()).to_equal("muted")
```

</details>

#### TextRole.Danger wire is 'danger'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TextRole.Danger.to_wire()).to_equal("danger")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/05_design/ui_typed_core_rfc.md](doc/05_design/ui_typed_core_rfc.md)


</details>
