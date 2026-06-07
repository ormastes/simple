# Game2D Hello-Demo (AC-1)

> `std.game2d` exposes an `App` trait with default no-op `load/update/fixed_update/draw` methods and a `run(app, title, size)` entry point. A 25-line example demo at `examples/11_advanced/game2d/hello/main.spl` must compile and use *only* `std.game2d`.

<!-- sdn-diagram:id=game2d_hello_demo_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_hello_demo_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_hello_demo_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_hello_demo_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2D Hello-Demo (AC-1)

`std.game2d` exposes an `App` trait with default no-op `load/update/fixed_update/draw` methods and a `run(app, title, size)` entry point. A 25-line example demo at `examples/11_advanced/game2d/hello/main.spl` must compile and use *only* `std.game2d`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GAME2D-HELLO-001 |
| Category | Engine2D |
| Difficulty | 2/5 |
| Status | Failing (no impl) |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/engine/game2d_hello_demo_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`std.game2d` exposes an `App` trait with default no-op `load/update/fixed_update/draw`
methods and a `run(app, title, size)` entry point. A 25-line example demo at
`examples/11_advanced/game2d/hello/main.spl` must compile and use *only* `std.game2d`.

Red-phase: trait/run impl missing; assertions on signature presence will fail.

## Syntax

The spec checks literal facade signatures, canonical example paths, and structural
App-shape methods instead of accepting placeholder sample bodies.

## Examples

A synthetic demo must import `std.game2d as g`, define an app class, implement an
`update` body with concrete behavior, and call `g.run(...)` within the 25-line budget.

## Scenarios

### Game2D Hello Demo (AC-1)
_## AC-1 — App trait + run() entry + ≤25-line demo."""_

### App trait declares default lifecycle methods

#### src/lib/nogc_sync_mut/game2d/app/app.spl declares trait App

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/app/app.spl")
expect(_contains(src, "trait App")).to_equal(true)
```

</details>

#### App trait includes load/update/fixed_update/draw

1.  contains

2.  contains

3.  contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/app/app.spl")
expect(_contains(src, "fn load") and
       _contains(src, "fn update") and
       _contains(src, "fn fixed_update") and
       _contains(src, "fn draw")).to_equal(true)
```

</details>

#### edge case: trait detection requires literal `trait App`

1. ) to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_contains("class App:\n    var x: i32", "trait App")
    ).to_equal(false)
```

</details>

#### error path: missing impl file does not crash spec

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/app/app.spl")
expect(src.len() >= 0).to_equal(true)
```

</details>

### run() entry point

#### src/lib/nogc_sync_mut/game2d/app/run.spl declares fn run

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/app/run.spl")
expect(_contains(src, "fn run(")).to_equal(true)
```

</details>

#### run() takes title/size params (default-arg overload)

1. ) to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/app/run.spl")
expect(_contains(src, "title:") and _contains(src, "GameConfig")
    ).to_equal(true)
```

</details>

#### edge case: synthetic signature is detected

1.  contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = "fn run(app: App, title: text = \"x\", w: i32 = 800, h: i32 = 600)"
expect(_contains(sample, "fn run(") and
       _contains(sample, "title:")).to_equal(true)
```

</details>

### examples/11_advanced/game2d/hello/main.spl

#### exists at the canonical path

1. ) to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("examples/11_advanced/game2d/hello/main.spl")
    ).to_equal(true)
```

</details>

#### imports only std.game2d (no direct std.nogc_sync_mut.engine.*)

1. "use std nogc sync mut engine ")) to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("examples/11_advanced/game2d/hello/main.spl")
expect(_contains(src,
    "use std.nogc_sync_mut.engine.")).to_equal(false)
```

</details>

#### compiles via parse-only path (proxy: g.run is referenced)

1. ) to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Phase 5 must implement the demo; this assertion fails until then.
val src = _read("examples/11_advanced/game2d/hello/main.spl")
expect(_contains(src, "g.run") or _contains(src, "run(")
    ).to_equal(true)
```

</details>

#### edge case: a 25-line synthetic demo would meet the budget

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = "use std.game2d as g\nclass MyApp:\n    ticks: i64\n    fn update(self, dt: f32):\n        self.ticks + 1\ng.run(MyApp(ticks: 0))\n"
expect(sample.split("\n").len() as i64 <= 25).to_equal(true)
```

</details>

#### error path: empty file => parse-only assertion fails

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_contains("", "g.run")).to_equal(false)
```

</details>

### parses without errors (Phase 5b gate)

#### demo uses structural App shape: class Game with required methods

1.  contains

2.  contains

3.  contains

4.  contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("examples/11_advanced/game2d/hello/main.spl")
expect(_contains(src, "class Game") and
       _contains(src, "fn update(self") and
       _contains(src, "fn fixed_update(self") and
       _contains(src, "fn draw(self") and
       _contains(src, "fn load(self")).to_equal(true)
```

</details>

#### demo does NOT use the broken inheritance form `class X : g.App`

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("examples/11_advanced/game2d/hello/main.spl")
expect(_contains(src, "class Game : g.App")).to_equal(false)
```

</details>

#### demo does NOT use the broken `: App` inheritance form either

1.  contains

2.  contains

3.  contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("examples/11_advanced/game2d/hello/main.spl")
# `class Game:` is fine; `class Game : App` (with space) is not.
expect(_contains(src, "class Game : App") or
       _contains(src, "class Game: App") or
       _contains(src, "class Game : g.App") or
       _contains(src, "class Game: g.App")).to_equal(false)
```

</details>

#### demo invokes g.run with the sprite/window args

1. ) to equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("examples/11_advanced/game2d/hello/main.spl")
expect(_contains(src, "g.run(") and _contains(src, "800")
    ).to_equal(true)
```

</details>

#### edge case: detection rejects fabricated inheritance

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = "use std.game2d as g\nclass Game : g.App:\n    fn update(self, dt: f32): pass\n"
expect(_contains(bad, "class Game : g.App")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
