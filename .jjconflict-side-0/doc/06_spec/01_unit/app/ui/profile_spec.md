# Profile Specification

> <details>

<!-- sdn-diagram:id=profile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=profile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

profile_spec -> std
profile_spec -> common
profile_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=profile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 54 | 54 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Profile Specification

## Scenarios

### detect_orientation

#### returns Landscape when width > height

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_orientation(120, 40)).to_equal(Orientation.Landscape)
```

</details>

#### returns Portrait when height > width

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_orientation(40, 120)).to_equal(Orientation.Portrait)
```

</details>

#### returns Square when width == height

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_orientation(100, 100)).to_equal(Orientation.Square)
```

</details>

#### returns Landscape for typical terminal 80x24

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_orientation(80, 24)).to_equal(Orientation.Landscape)
```

</details>

#### returns Portrait for tall terminal 40x60

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_orientation(40, 60)).to_equal(Orientation.Portrait)
```

</details>

### classify with default breakpoints

#### returns Compact below 600

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = default_breakpoints()
expect(classify(599, bp)).to_equal(SizeClass.Compact)
```

</details>

#### returns Regular at 600

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = default_breakpoints()
expect(classify(600, bp)).to_equal(SizeClass.Regular)
```

</details>

#### returns Regular below 840

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = default_breakpoints()
expect(classify(839, bp)).to_equal(SizeClass.Regular)
```

</details>

#### returns Expanded at 840

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = default_breakpoints()
expect(classify(840, bp)).to_equal(SizeClass.Expanded)
```

</details>

### classify with terminal breakpoints

#### returns Compact below 80

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = terminal_breakpoints()
expect(classify(79, bp)).to_equal(SizeClass.Compact)
```

</details>

#### returns Regular at 80

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = terminal_breakpoints()
expect(classify(80, bp)).to_equal(SizeClass.Regular)
```

</details>

#### returns Expanded at 160

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = terminal_breakpoints()
expect(classify(160, bp)).to_equal(SizeClass.Expanded)
```

</details>

### breakpoints_for_backend

#### returns terminal breakpoints for tui

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = breakpoints_for_backend("tui")
expect(bp.compact_max).to_equal(80)
```

</details>

#### returns default breakpoints for web

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = breakpoints_for_backend("web")
expect(bp.compact_max).to_equal(600)
```

</details>

#### returns default breakpoints for none

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = breakpoints_for_backend("none")
expect(bp.compact_max).to_equal(600)
```

</details>

### compute_profile

#### computes landscape regular for 80x24 tui

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vp = new_viewport(80, 24, "tui")
val p = compute_profile(vp)
expect(p.orientation).to_equal(Orientation.Landscape)
expect(p.horizontal).to_equal(SizeClass.Regular)
expect(p.vertical).to_equal(SizeClass.Compact)
```

</details>

#### computes portrait compact for 40x60 tui

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vp = new_viewport(40, 60, "tui")
val p = compute_profile(vp)
expect(p.orientation).to_equal(Orientation.Portrait)
expect(p.horizontal).to_equal(SizeClass.Compact)
```

</details>

#### computes landscape expanded for 1920x1080 web

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vp = new_viewport(1920, 1080, "web")
val p = compute_profile(vp)
expect(p.orientation).to_equal(Orientation.Landscape)
expect(p.horizontal).to_equal(SizeClass.Expanded)
```

</details>

### LayoutProfile

#### is_landscape returns true for Landscape

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = default_profile()
expect(p.is_landscape()).to_equal(true)
```

</details>

#### is_landscape returns true for Square

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = LayoutProfile(
    horizontal: SizeClass.Regular,
    vertical: SizeClass.Regular,
    orientation: Orientation.Square,
    width: 100, height: 100
)
expect(p.is_landscape()).to_equal(true)
```

</details>

#### is_portrait returns true for Portrait

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = LayoutProfile(
    horizontal: SizeClass.Compact,
    vertical: SizeClass.Regular,
    orientation: Orientation.Portrait,
    width: 40, height: 120
)
expect(p.is_portrait()).to_equal(true)
```

</details>

#### is_compact returns true for Compact horizontal

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = LayoutProfile(
    horizontal: SizeClass.Compact,
    vertical: SizeClass.Compact,
    orientation: Orientation.Portrait,
    width: 40, height: 60
)
expect(p.is_compact()).to_equal(true)
```

</details>

#### describe includes orientation and size

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = default_profile()
val desc = p.describe()
expect(desc).to_contain("landscape")
expect(desc).to_contain("80x24")
```

</details>

### ProfileSet

#### resolves to default when no profiles set

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_node = column("default", [])
val ps = ProfileSet.new(default_node)
val resolved = ps.resolve(Orientation.Landscape)
expect(resolved.id).to_equal("default")
```

</details>

#### resolves landscape profile when set

- var ps = ProfileSet new
- ps = ps with landscape
   - Expected: resolved.id equals `landscape`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_node = column("default", [])
val h_node = row("landscape", [])
var ps = ProfileSet.new(default_node)
ps = ps.with_landscape(h_node)
val resolved = ps.resolve(Orientation.Landscape)
expect(resolved.id).to_equal("landscape")
```

</details>

#### resolves portrait profile when set

- var ps = ProfileSet new
- ps = ps with portrait
   - Expected: resolved.id equals `portrait`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_node = column("default", [])
val v_node = column("portrait", [])
var ps = ProfileSet.new(default_node)
ps = ps.with_portrait(v_node)
val resolved = ps.resolve(Orientation.Portrait)
expect(resolved.id).to_equal("portrait")
```

</details>

#### falls back to default for unset orientation

- var ps = ProfileSet new
- ps = ps with landscape
   - Expected: resolved.id equals `default`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_node = column("default", [])
val h_node = row("landscape", [])
var ps = ProfileSet.new(default_node)
ps = ps.with_landscape(h_node)
val resolved = ps.resolve(Orientation.Portrait)
expect(resolved.id).to_equal("default")
```

</details>

#### resolves Square as Landscape

- var ps = ProfileSet new
- ps = ps with landscape
   - Expected: resolved.id equals `landscape`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_node = column("default", [])
val h_node = row("landscape", [])
var ps = ProfileSet.new(default_node)
ps = ps.with_landscape(h_node)
val resolved = ps.resolve(Orientation.Square)
expect(resolved.id).to_equal("landscape")
```

</details>

#### has_profile returns false when not set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ps = ProfileSet.new(column("d", []))
expect(ps.has_profile(Orientation.Landscape)).to_equal(false)
expect(ps.has_profile(Orientation.Portrait)).to_equal(false)
```

</details>

#### has_profile returns true when set

- var ps = ProfileSet new
- ps = ps with landscape
   - Expected: ps.has_profile(Orientation.Landscape) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ps = ProfileSet.new(column("d", []))
ps = ps.with_landscape(row("h", []))
expect(ps.has_profile(Orientation.Landscape)).to_equal(true)
```

</details>

### ProfileResolver

#### starts with landscape orientation for default 80x24

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolver = ProfileResolver.new()
expect(resolver.orientation()).to_equal(Orientation.Landscape)
```

</details>

#### detects orientation change after update

- var resolver = ProfileResolver new
- resolver update
   - Expected: resolver.orientation_changed(old) is true
   - Expected: resolver.orientation() equals `Orientation.Portrait`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resolver = ProfileResolver.new()
val old = resolver.orientation()
resolver.update(new_viewport(40, 60, "tui"))
expect(resolver.orientation_changed(old)).to_equal(true)
expect(resolver.orientation()).to_equal(Orientation.Portrait)
```

</details>

#### no change when orientation stays same

- var resolver = ProfileResolver new
- resolver update
   - Expected: resolver.orientation_changed(old) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resolver = ProfileResolver.new()
val old = resolver.orientation()
resolver.update(new_viewport(120, 40, "tui"))
expect(resolver.orientation_changed(old)).to_equal(false)
```

</details>

#### updates size classes on viewport change

- var resolver = ProfileResolver new
- resolver update
   - Expected: resolver.horizontal_class() equals `SizeClass.Expanded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resolver = ProfileResolver.new()
resolver.update(new_viewport(200, 40, "tui"))
expect(resolver.horizontal_class()).to_equal(SizeClass.Expanded)
```

</details>

### adaptive

#### creates profile set with both orientations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ps = adaptive("main", row("h", []), column("v", []))
expect(ps.has_profile(Orientation.Landscape)).to_equal(true)
expect(ps.has_profile(Orientation.Portrait)).to_equal(true)
```

</details>

### with_profile

#### creates profile set with one alternate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ps = with_profile(row("default", []), Orientation.Portrait, column("alt", []))
expect(ps.has_profile(Orientation.Portrait)).to_equal(true)
expect(ps.has_profile(Orientation.Landscape)).to_equal(false)
```

</details>

### adaptive_stack

#### produces hbox layout in landscape

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = LayoutProfile(
    horizontal: SizeClass.Regular, vertical: SizeClass.Compact,
    orientation: Orientation.Landscape, width: 120, height: 40
)
val node = adaptive_stack("s", [text_widget("a", "hello")], p)
expect(node.layout_name()).to_equal("hbox")
```

</details>

#### produces vbox layout in portrait

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = LayoutProfile(
    horizontal: SizeClass.Compact, vertical: SizeClass.Regular,
    orientation: Orientation.Portrait, width: 40, height: 120
)
val node = adaptive_stack("s", [text_widget("a", "hello")], p)
expect(node.layout_name()).to_equal("vbox")
```

</details>

### adaptive_sidebar

#### hides sidebar in Compact

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = LayoutProfile(
    horizontal: SizeClass.Compact, vertical: SizeClass.Compact,
    orientation: Orientation.Portrait, width: 40, height: 60
)
val sb = panel("sb", "Nav", [])
val ct = panel("ct", "Main", [])
val node = adaptive_sidebar("layout", sb, ct, p)
val children = node.children()
expect(children.len()).to_equal(1)
```

</details>

#### shows sidebar in Regular

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = LayoutProfile(
    horizontal: SizeClass.Regular, vertical: SizeClass.Compact,
    orientation: Orientation.Landscape, width: 120, height: 40
)
val sb = panel("sb", "Nav", [])
val ct = panel("ct", "Main", [])
val node = adaptive_sidebar("layout", sb, ct, p)
val children = node.children()
expect(children.len()).to_equal(2)
```

</details>

### adaptive_grid

#### sets 1 column in Compact

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = LayoutProfile(
    horizontal: SizeClass.Compact, vertical: SizeClass.Compact,
    orientation: Orientation.Portrait, width: 40, height: 60
)
val node = adaptive_grid("g", [text_widget("a", "1")], p)
expect(node.get_prop("columns")).to_equal("1")
```

</details>

#### sets 2 columns in Regular

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = LayoutProfile(
    horizontal: SizeClass.Regular, vertical: SizeClass.Compact,
    orientation: Orientation.Landscape, width: 120, height: 40
)
val node = adaptive_grid("g", [text_widget("a", "1")], p)
expect(node.get_prop("columns")).to_equal("2")
```

</details>

#### sets 3 columns in Expanded

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = LayoutProfile(
    horizontal: SizeClass.Expanded, vertical: SizeClass.Regular,
    orientation: Orientation.Landscape, width: 200, height: 60
)
val node = adaptive_grid("g", [text_widget("a", "1")], p)
expect(node.get_prop("columns")).to_equal("3")
```

</details>

### responsive

#### picks compact variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = LayoutProfile(
    horizontal: SizeClass.Compact, vertical: SizeClass.Compact,
    orientation: Orientation.Portrait, width: 40, height: 60
)
val c = text_widget("c", "compact")
val r = text_widget("r", "regular")
val e = text_widget("e", "expanded")
val node = responsive("resp", p, c, r, e)
expect(node.id).to_equal("c")
```

</details>

#### picks regular variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = LayoutProfile(
    horizontal: SizeClass.Regular, vertical: SizeClass.Compact,
    orientation: Orientation.Landscape, width: 120, height: 40
)
val c = text_widget("c", "compact")
val r = text_widget("r", "regular")
val e = text_widget("e", "expanded")
val node = responsive("resp", p, c, r, e)
expect(node.id).to_equal("r")
```

</details>

### responsive_if_wide

#### picks narrow in Compact

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = LayoutProfile(
    horizontal: SizeClass.Compact, vertical: SizeClass.Compact,
    orientation: Orientation.Portrait, width: 40, height: 60
)
val n = text_widget("narrow", "n")
val w = text_widget("wide", "w")
val node = responsive_if_wide("resp", p, n, w)
expect(node.id).to_equal("narrow")
```

</details>

#### picks wide in Regular

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = LayoutProfile(
    horizontal: SizeClass.Regular, vertical: SizeClass.Compact,
    orientation: Orientation.Landscape, width: 120, height: 40
)
val n = text_widget("narrow", "n")
val w = text_widget("wide", "w")
val node = responsive_if_wide("resp", p, n, w)
expect(node.id).to_equal("wide")
```

</details>

### Viewport orientation

#### is_landscape for wide viewport

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vp = new_viewport(120, 40, "tui")
expect(vp.is_landscape()).to_equal(true)
```

</details>

#### is_portrait for tall viewport

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vp = new_viewport(40, 120, "tui")
expect(vp.is_portrait()).to_equal(true)
```

</details>

#### orientation returns correct enum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vp = new_viewport(80, 24, "tui")
expect(vp.orientation()).to_equal(Orientation.Landscape)
```

</details>

#### size_class returns Regular for 80-col tui

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vp = new_viewport(80, 24, "tui")
expect(vp.size_class()).to_equal(SizeClass.Regular)
```

</details>

### UISession profiles

#### creates session with default profile resolver

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = UITree.new(column("root", []))
val session = new_session(tree)
expect(session.current_orientation()).to_equal(Orientation.Landscape)
```

</details>

#### register_profile_set stores profiles

- var session = new session
- session register profile set
   - Expected: session.profile_sets.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = UITree.new(column("root", []))
var session = new_session(tree)
val ps = adaptive("main", row("h", []), column("v", []))
session.register_profile_set("main", ps)
expect(session.profile_sets.len()).to_equal(1)
```

</details>

#### register_profile_set replaces existing entry

- var session = new session
- session register profile set
- session register profile set
   - Expected: session.profile_sets.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = UITree.new(column("root", []))
var session = new_session(tree)
val ps1 = adaptive("main", row("h1", []), column("v1", []))
val ps2 = adaptive("main", row("h2", []), column("v2", []))
session.register_profile_set("main", ps1)
session.register_profile_set("main", ps2)
expect(session.profile_sets.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/profile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- detect_orientation
- classify with default breakpoints
- classify with terminal breakpoints
- breakpoints_for_backend
- compute_profile
- LayoutProfile
- ProfileSet
- ProfileResolver
- adaptive
- with_profile
- adaptive_stack
- adaptive_sidebar
- adaptive_grid
- responsive
- responsive_if_wide
- Viewport orientation
- UISession profiles

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 54 |
| Active scenarios | 54 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
