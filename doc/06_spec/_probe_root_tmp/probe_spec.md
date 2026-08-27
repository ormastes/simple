# model3d nested node embedding

> `Node3` gains a `children: [Node3]` list so scenes can express simple object-in-object embedding ("rendering inside rendering", Lane D — minimal). A child's `center` is RELATIVE to its parent's world-composed center; positions compose additively down the tree. `size` stays an absolute box extent in world units (not a normalized scale factor), so it deliberately does NOT compose — a child's box is never scaled by its parent's size. `Scene3.embed(parent_name, child)` finds a node by name (searching the whole tree) and appends `child` under it, returning false if no such node exists. Rendering traversal visits parent-then-children, translating each child by its parent's already-composed world offset, capped at 8 levels deep. Flat scenes (no children — the common case) render identically to before.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# model3d nested node embedding

`Node3` gains a `children: [Node3]` list so scenes can express simple object-in-object embedding ("rendering inside rendering", Lane D — minimal). A child's `center` is RELATIVE to its parent's world-composed center; positions compose additively down the tree. `size` stays an absolute box extent in world units (not a normalized scale factor), so it deliberately does NOT compose — a child's box is never scaled by its parent's size. `Scene3.embed(parent_name, child)` finds a node by name (searching the whole tree) and appends `child` under it, returning false if no such node exists. Rendering traversal visits parent-then-children, translating each child by its parent's already-composed world offset, capped at 8 levels deep. Flat scenes (no children — the common case) render identically to before.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #model3d-nested-nodes |
| Category | App / 3D Scene Model |
| Status | Implemented |
| Source | `test/_probe_root_tmp/probe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`Node3` gains a `children: [Node3]` list so scenes can express simple
object-in-object embedding ("rendering inside rendering", Lane D — minimal).
A child's `center` is RELATIVE to its parent's world-composed center;
positions compose additively down the tree. `size` stays an absolute box
extent in world units (not a normalized scale factor), so it deliberately
does NOT compose — a child's box is never scaled by its parent's size.
`Scene3.embed(parent_name, child)` finds a node by name (searching the whole
tree) and appends `child` under it, returning false if no such node exists.
Rendering traversal visits parent-then-children, translating each child by
its parent's already-composed world offset, capped at 8 levels deep. Flat
scenes (no children — the common case) render identically to before.

## Key Concepts

| Concept | Description |
|---------|-------------|
| `children: [Node3]` | Default-empty list on every `Node3`; nesting is opt-in |
| Position composition | `world.center = node.center + parent.world.center` (recursive, additive) |
| Size composition | NOT composed — `size` is absolute world-unit box extent, constraint by design |
| `node_world_positions(scene)` | Pure helper: flattens the tree into `(name, world center)` pairs, parent before children |
| `Scene3.embed(parent_name, child)` | Depth-first name search + append; `false` if `parent_name` is not found |
| Depth cap | 8 levels, shared by rendering traversal and `node_world_positions` |

## Note on CLI-level testing

`test/02_integration/app/model3d/model3d_cli_spec.spl` exercises this app
through `bin/simple src/app/model3d/main.spl <args>`. In this environment
that entry path is currently broken independently of this change: a fresh
throwaway `.spl` script confirms `get_cli_args()` returns the *script path
itself* as `args[0]` when invoked as `bin/simple <file.spl> <args...>`
(reproduced with a script that has nothing to do with model3d), so
`sub == "src/app/model3d/main.spl"` and every subcommand look-up fails with
"unknown subcommand". This matches the already-tracked
"`build bootstrap` entry-point regression" follow-up in project memory, not
something introduced here. This spec therefore drives the same pure
functions (`render_scene`, `ppm_text`, `node_world_positions`, `Scene3.embed`,
`load_scene`-independent direct construction) directly via `use
app.model3d.main.{...}`, which is unaffected by the CLI arg-parsing bug.
Separately, `load_scene(...)` on a real fixture path stack-overflows when
called through this direct-import path (reproduced with a minimal
`file_read` + `std.sdn.parse` probe showing `parse` itself does not
overflow, isolating the fault to `load_scene`'s call chain specifically
under this import) — the flat-scene regression check below instead builds
the fixture's exact node graph with the public `Node3`/`Scene3`
constructors, so it still asserts the same pixel oracle without exercising
that separate, pre-existing path.

## Scenarios

### model3d nested nodes: world position composition

#### renders a child at its parent-relative offset composed into world space

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders a child at its parent-relative offset composed into world space
- Build a parent at the origin with one child offset by (1, 0, 0)
- Then the flattened world positions are parent-first, child composed
   - Expected: positions.len() equals `2`
   - Expected: positions[0].name equals `parent`
   - Expected: positions[0].pos.x equals `0.0`
   - Expected: positions[1].name equals `child`
   - Expected: positions[1].pos.x equals `1.0`
   - Expected: positions[1].pos.y equals `0.0`
   - Expected: positions[1].pos.z equals `0.0`
- Then a coarse raster smoke shows the child's color in the frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PROBEROOTTMP
step("renders a child at its parent-relative offset composed into world space")
step("Build a parent at the origin with one child offset by (1, 0, 0)")
var child = mk_node("child", 1.0, 0.0, 0.0, 0xFF00FF00)
var parent = mk_node("parent", 0.0, 0.0, 0.0, 0xFFCC3020)
parent.children = [child]
val scene = mk_scene([parent])

step("Then the flattened world positions are parent-first, child composed")
val positions = node_world_positions(scene)
expect(positions.len()).to_equal(2)
expect(positions[0].name).to_equal("parent")
expect(positions[0].pos.x).to_equal(0.0)
expect(positions[1].name).to_equal("child")
expect(positions[1].pos.x).to_equal(1.0)
expect(positions[1].pos.y).to_equal(0.0)
expect(positions[1].pos.z).to_equal(0.0)

step("Then a coarse raster smoke shows the child's color in the frame")
val pixels = render_scene(scene, 64, 48)
val ppm = ppm_text(pixels, 64, 48)
expect(ppm).to_contain("0 255 0")
```

</details>

#### composes offsets across two levels of nesting

- composes offsets across two levels of nesting
- Build grandparent -> parent (+1,0,0) -> child (+1,0,0)
- Then each level's world x is the running sum of relative offsets
   - Expected: positions.len() equals `3`
   - Expected: positions[0].name equals `grandparent`
   - Expected: positions[0].pos.x equals `1.0`
   - Expected: positions[1].name equals `parent`
   - Expected: positions[1].pos.x equals `2.0`
   - Expected: positions[2].name equals `child`
   - Expected: positions[2].pos.x equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PROBEROOTTMP
step("composes offsets across two levels of nesting")
step("Build grandparent -> parent (+1,0,0) -> child (+1,0,0)")
var child = mk_node("child", 1.0, 0.0, 0.0, 0xFF0000FF)
var parent = mk_node("parent", 1.0, 0.0, 0.0, 0xFF00FF00)
parent.children = [child]
var grandparent = mk_node("grandparent", 1.0, 0.0, 0.0, 0xFFCC3020)
grandparent.children = [parent]
val scene = mk_scene([grandparent])

step("Then each level's world x is the running sum of relative offsets")
val positions = node_world_positions(scene)
expect(positions.len()).to_equal(3)
expect(positions[0].name).to_equal("grandparent")
expect(positions[0].pos.x).to_equal(1.0)
expect(positions[1].name).to_equal("parent")
expect(positions[1].pos.x).to_equal(2.0)
expect(positions[2].name).to_equal("child")
expect(positions[2].pos.x).to_equal(3.0)
```

</details>

#### leaves a flat scene's world positions identical to its local centers

- leaves a flat scene's world positions identical to its local centers
- Build two top-level nodes with no children
- Then world positions equal each node's own (unmodified) center
   - Expected: positions.len() equals `2`
   - Expected: positions[0].pos.x equals `1.0`
   - Expected: positions[0].pos.y equals `2.0`
   - Expected: positions[0].pos.z equals `3.0`
   - Expected: positions[1].pos.x equals `-1.0`
   - Expected: positions[1].pos.y equals `-2.0`
   - Expected: positions[1].pos.z equals `-3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PROBEROOTTMP
step("leaves a flat scene's world positions identical to its local centers")
step("Build two top-level nodes with no children")
val a = mk_node("a", 1.0, 2.0, 3.0, 0xFFAABBCC)
val b = mk_node("b", -1.0, -2.0, -3.0, 0xFF112233)
val scene = mk_scene([a, b])

step("Then world positions equal each node's own (unmodified) center")
val positions = node_world_positions(scene)
expect(positions.len()).to_equal(2)
expect(positions[0].pos.x).to_equal(1.0)
expect(positions[0].pos.y).to_equal(2.0)
expect(positions[0].pos.z).to_equal(3.0)
expect(positions[1].pos.x).to_equal(-1.0)
expect(positions[1].pos.y).to_equal(-2.0)
expect(positions[1].pos.z).to_equal(-3.0)
```

</details>

### model3d nested nodes: flat-scene render regression

#### renders a flat two-node scene to the same pixel oracle as before nesting existed

- renders a flat two-node scene to the same pixel oracle as before nesting existed
- Build the same two-node fixture the CLI spec renders (cube + floor)
- Render at 96x72, matching model3d_cli_spec.spl's dimensions
   - Expected: lines[0] equals `P3`
   - Expected: lines[1] equals `96 72`
- Then the center pixel is exactly the cube color, corners are background
   - Expected: ppm_pixel_line(lines, 96, 48, 36) equals `204 48 32`
   - Expected: ppm_pixel_line(lines, 96, 0, 0) equals `32 48 64`
   - Expected: ppm_pixel_line(lines, 96, 95, 0) equals `32 48 64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PROBEROOTTMP
step("renders a flat two-node scene to the same pixel oracle as before nesting existed")
step("Build the same two-node fixture the CLI spec renders (cube + floor)")
val cube = Node3(name: "cube", shape: "box", center: Vec3(x: 0.0, y: 0.0, z: 0.0), size: Vec3(x: 2.0, y: 2.0, z: 2.0), color: 0xFFCC3020, children: [])
val floor = Node3(name: "floor", shape: "box", center: Vec3(x: 0.0, y: -2.5, z: 0.0), size: Vec3(x: 8.0, y: 0.5, z: 8.0), color: 0xFF3060A0, children: [])
val scene = Scene3(name: "probe", background: 0xFF203040, eye: Vec3(x: 0.0, y: 0.0, z: 6.0), target: Vec3(x: 0.0, y: 0.0, z: 0.0), fov_deg: 60.0, nodes: [cube, floor])

step("Render at 96x72, matching model3d_cli_spec.spl's dimensions")
val pixels = render_scene(scene, 96, 72)
val ppm = ppm_text(pixels, 96, 72)
val lines = ppm.split("\n")
expect(lines[0]).to_equal("P3")
expect(lines[1]).to_equal("96 72")

step("Then the center pixel is exactly the cube color, corners are background")
expect(ppm_pixel_line(lines, 96, 48, 36)).to_equal("204 48 32")
expect(ppm_pixel_line(lines, 96, 0, 0)).to_equal("32 48 64")
expect(ppm_pixel_line(lines, 96, 95, 0)).to_equal("32 48 64")
```

</details>

#### does not draw anything extra for a node with an empty children list

- does not draw anything extra for a node with an empty children list
- Render a lone node whose children field is the default empty list
- Then no child color (e.g. pure green) ever appears in the frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PROBEROOTTMP
step("does not draw anything extra for a node with an empty children list")
step("Render a lone node whose children field is the default empty list")
val lone = mk_node("lone", 0.0, 0.0, 0.0, 0xFFCC3020)
val scene = mk_scene([lone])
val pixels = render_scene(scene, 64, 48)
val ppm = ppm_text(pixels, 64, 48)

step("Then no child color (e.g. pure green) ever appears in the frame")
assert_false(ppm.contains("0 255 0"))
```

</details>

### model3d nested nodes: Scene3.embed

#### appends a child under a top-level node found by name

- appends a child under a top-level node found by name
- Embed a new child under the top-level 'parent' node
- Then embed reports success and the child is attached
   - Expected: ok is true
   - Expected: scene.nodes[0].children.len() equals `1`
   - Expected: scene.nodes[0].children[0].name equals `child`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PROBEROOTTMP
step("appends a child under a top-level node found by name")
step("Embed a new child under the top-level 'parent' node")
val parent = mk_node("parent", 0.0, 0.0, 0.0, 0xFFCC3020)
var scene = mk_scene([parent])
val child = mk_node("child", 1.0, 0.0, 0.0, 0xFF00FF00)
val ok = scene.embed("parent", child)

step("Then embed reports success and the child is attached")
expect(ok).to_equal(true)
expect(scene.nodes[0].children.len()).to_equal(1)
expect(scene.nodes[0].children[0].name).to_equal("child")
```

</details>

#### finds a nested (non-top-level) parent by name, searching the whole tree

- finds a nested (non-top-level) parent by name, searching the whole tree
- Embed under a grandchild two levels deep
   - Expected: ok1 is true
- Then the leaf lands under 'mid', which is under 'top'
   - Expected: ok2 is true
   - Expected: scene.nodes[0].name equals `top`
   - Expected: scene.nodes[0].children[0].name equals `mid`
   - Expected: scene.nodes[0].children[0].children[0].name equals `leaf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PROBEROOTTMP
step("finds a nested (non-top-level) parent by name, searching the whole tree")
step("Embed under a grandchild two levels deep")
var mid = mk_node("mid", 1.0, 0.0, 0.0, 0xFF00FF00)
val top = mk_node("top", 0.0, 0.0, 0.0, 0xFFCC3020)
var scene = mk_scene([top])
val ok1 = scene.embed("top", mid)
expect(ok1).to_equal(true)

val leaf = mk_node("leaf", 1.0, 0.0, 0.0, 0xFF0000FF)
val ok2 = scene.embed("mid", leaf)

step("Then the leaf lands under 'mid', which is under 'top'")
expect(ok2).to_equal(true)
expect(scene.nodes[0].name).to_equal("top")
expect(scene.nodes[0].children[0].name).to_equal("mid")
expect(scene.nodes[0].children[0].children[0].name).to_equal("leaf")
```

</details>

#### returns false and leaves the scene unchanged when the parent name is not found

- returns false and leaves the scene unchanged when the parent name is not found
- Attempt to embed under a name that does not exist in the scene
- Then embed reports failure and no node gained children
   - Expected: ok is false
   - Expected: scene.nodes[0].children.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PROBEROOTTMP
step("returns false and leaves the scene unchanged when the parent name is not found")
step("Attempt to embed under a name that does not exist in the scene")
val parent = mk_node("parent", 0.0, 0.0, 0.0, 0xFFCC3020)
var scene = mk_scene([parent])
val child = mk_node("child", 1.0, 0.0, 0.0, 0xFF00FF00)
val ok = scene.embed("no_such_node", child)

step("Then embed reports failure and no node gained children")
expect(ok).to_equal(false)
expect(scene.nodes[0].children.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PROBEROOTTMP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6344f696881a480a9172617e2907f35228b7d446ee6e233ce91b62c19d11fe70`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6344f696881a480a9172617e2907f35228b7d446ee6e233ce91b62c19d11fe70`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6344f696881a480a9172617e2907f35228b7d446ee6e233ce91b62c19d11fe70`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/_probe_root_tmp/probe_spec.spl
mirror: doc/06_spec/_probe_root_tmp/probe_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/_probe_root_tmp/probe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/_probe_root_tmp/probe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/_probe_root_tmp/probe_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 18 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/_probe_root_tmp/probe_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a child at its parent-relative offset composed into world space' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/_probe_root_tmp/probe_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'composes offsets across two levels of nesting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/_probe_root_tmp/probe_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves a flat scene's world positions identical to its local centers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
