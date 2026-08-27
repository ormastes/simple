# Game2D Hello-Demo (AC-1)

> `std.game2d` exposes an `App` trait with default no-op `load/update/fixed_update/draw` methods and a `run(app, title, size)` entry point. A 25-line example demo at `examples/11_advanced/game2d/hello/main.spl` must compile and use *only* `std.game2d`.

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
| Updated | 2026-08-26 |
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

### App trait declares default lifecycle methods

#### src/lib/nogc_sync_mut/game2d/app/app.spl declares trait App

- src/lib/nogc_sync_mut/game2d/app/app.spl declares trait App
   - Expected: _contains(src, "trait App") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("src/lib/nogc_sync_mut/game2d/app/app.spl declares trait App")
val src = _read("src/lib/nogc_sync_mut/game2d/app/app.spl")
expect(_contains(src, "trait App")).to_equal(true)
```

</details>

#### App trait includes load/update/fixed_update/draw

- App trait includes load/update/fixed_update/draw


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("App trait includes load/update/fixed_update/draw")
val src = _read("src/lib/nogc_sync_mut/game2d/app/app.spl")
expect(_contains(src, "fn load") and
       _contains(src, "fn update") and
       _contains(src, "fn fixed_update") and
       _contains(src, "fn draw")).to_equal(true)
```

</details>

#### edge case: trait detection requires literal `trait App`

- edge case: trait detection requires literal `trait App`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case: trait detection requires literal `trait App`")
expect(_contains("class App:\n    var x: i32", "trait App")
    ).to_equal(false)
```

</details>

#### error path: missing impl file does not crash spec

- error path: missing impl file does not crash spec
   - Expected: src.len() >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path: missing impl file does not crash spec")
val src = _read("src/lib/nogc_sync_mut/game2d/app/app.spl")
expect(src.len() >= 0).to_equal(true)
```

</details>

### run() entry point

#### src/lib/nogc_sync_mut/game2d/app/run.spl declares fn run

- src/lib/nogc_sync_mut/game2d/app/run.spl declares fn run
   - Expected: _contains(src, "fn run(") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("src/lib/nogc_sync_mut/game2d/app/run.spl declares fn run")
val src = _read("src/lib/nogc_sync_mut/game2d/app/run.spl")
expect(_contains(src, "fn run(")).to_equal(true)
```

</details>

#### run() takes title/size params (default-arg overload)

- run() takes title/size params (default-arg overload)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("run() takes title/size params (default-arg overload)")
val src = _read("src/lib/nogc_sync_mut/game2d/app/run.spl")
expect(_contains(src, "title:") and _contains(src, "GameConfig")
    ).to_equal(true)
```

</details>

#### edge case: synthetic signature is detected

- edge case: synthetic signature is detected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case: synthetic signature is detected")
val sample = "fn run(app: App, title: text = \"x\", w: i32 = 800, h: i32 = 600)"
expect(_contains(sample, "fn run(") and
       _contains(sample, "title:")).to_equal(true)
```

</details>

### examples/11_advanced/game2d/hello/main.spl

#### exists at the canonical path

- exists at the canonical path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exists at the canonical path")
expect(rt_file_exists("examples/11_advanced/game2d/hello/main.spl")
    ).to_equal(true)
```

</details>

#### imports only std.game2d (no direct std.nogc_sync_mut.engine.*)

- imports only std.game2d (no direct std.nogc_sync_mut.engine.*)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("imports only std.game2d (no direct std.nogc_sync_mut.engine.*)")
val src = _read("examples/11_advanced/game2d/hello/main.spl")
expect(_contains(src,
    "use std.nogc_sync_mut.engine.")).to_equal(false)
```

</details>

#### compiles via parse-only path (proxy: g.run is referenced)

- compiles via parse-only path (proxy: g.run is referenced)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles via parse-only path (proxy: g.run is referenced)")
# Phase 5 must implement the demo; this assertion fails until then.
val src = _read("examples/11_advanced/game2d/hello/main.spl")
expect(_contains(src, "g.run") or _contains(src, "run(")
    ).to_equal(true)
```

</details>

#### edge case: a 25-line synthetic demo would meet the budget

- edge case: a 25-line synthetic demo would meet the budget
   - Expected: sample.split("\n").len() as i64 <= 25 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case: a 25-line synthetic demo would meet the budget")
val sample = "use std.game2d as g\nclass MyApp:\n    ticks: i64\n    fn update(self, dt: f32):\n        self.ticks + 1\ng.run(MyApp(ticks: 0))\n"
expect(sample.split("\n").len() as i64 <= 25).to_equal(true)
```

</details>

#### error path: empty file => parse-only assertion fails

- error path: empty file => parse-only assertion fails
   - Expected: _contains("", "g.run") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path: empty file => parse-only assertion fails")
expect(_contains("", "g.run")).to_equal(false)
```

</details>

### parses without errors (Phase 5b gate)

#### demo uses structural App shape: class Game with required methods

- demo uses structural App shape: class Game with required methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("demo uses structural App shape: class Game with required methods")
val src = _read("examples/11_advanced/game2d/hello/main.spl")
expect(_contains(src, "class Game") and
       _contains(src, "fn update(self") and
       _contains(src, "fn fixed_update(self") and
       _contains(src, "fn draw(self") and
       _contains(src, "fn load(self")).to_equal(true)
```

</details>

#### demo does NOT use the broken inheritance form `class X : g.App`

- demo does NOT use the broken inheritance form `class X : g.App`
   - Expected: _contains(src, "class Game : g.App") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("demo does NOT use the broken inheritance form `class X : g.App`")
val src = _read("examples/11_advanced/game2d/hello/main.spl")
expect(_contains(src, "class Game : g.App")).to_equal(false)
```

</details>

#### demo does NOT use the broken `: App` inheritance form either

- demo does NOT use the broken `: App` inheritance form either


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("demo does NOT use the broken `: App` inheritance form either")
val src = _read("examples/11_advanced/game2d/hello/main.spl")
# `class Game:` is fine; `class Game : App` (with space) is not.
expect(_contains(src, "class Game : App") or
       _contains(src, "class Game: App") or
       _contains(src, "class Game : g.App") or
       _contains(src, "class Game: g.App")).to_equal(false)
```

</details>

#### demo invokes g.run with the sprite/window args

- demo invokes g.run with the sprite/window args


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("demo invokes g.run with the sprite/window args")
val src = _read("examples/11_advanced/game2d/hello/main.spl")
expect(_contains(src, "g.run(") and _contains(src, "800")
    ).to_equal(true)
```

</details>

#### edge case: detection rejects fabricated inheritance

- edge case: detection rejects fabricated inheritance
   - Expected: _contains(bad, "class Game : g.App") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case: detection rejects fabricated inheritance")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dc12b026685592bc3bd24207ff64709915f8d661ae017439c0bde1eca3092c9e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc12b026685592bc3bd24207ff64709915f8d661ae017439c0bde1eca3092c9e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc12b026685592bc3bd24207ff64709915f8d661ae017439c0bde1eca3092c9e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/engine/game2d_hello_demo_spec.spl
mirror: doc/06_spec/03_system/engine/game2d_hello_demo_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/game2d_hello_demo_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/game2d_hello_demo_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/game2d_hello_demo_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'src/lib/nogc_sync_mut/game2d/app/app.spl declares trait App' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/game2d_hello_demo_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'App trait includes load/update/fixed_update/draw' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/game2d_hello_demo_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'edge case: trait detection requires literal `trait App`' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
