# scene_generator_spec

> Scene Generator Tests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scene_generator_spec

Scene Generator Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/engine/scene_generator_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Scene Generator Tests

Tests SceneObject construction and properties, GeneratedScene serialization,
and SceneGenerator template management and scene generation.

## Scenarios

### SceneObject

### new

#### creates an object with type, name, and position

- creates an object with type, name, and position
   - Expected: obj.obj_type equals `tree`
   - Expected: obj.name equals `oak1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates an object with type, name, and position")
val obj = SceneObject.new("tree", "oak1", 10.0, 20.0)
expect(obj.obj_type).to_equal("tree")
expect(obj.name).to_equal("oak1")
```

</details>

### add_property

#### adds a property string

- adds a property string
   - Expected: obj.properties.len().to_i32() equals `2.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds a property string")
var obj = SceneObject.new("tree", "oak1", 5.0, 5.0)
obj.add_property("height: tall")
obj.add_property("color: green")
expect(obj.properties.len().to_i32()).to_equal(2.to_i32())
```

</details>

### GeneratedScene

### new

#### creates an empty scene with a name

- creates an empty scene with a name
   - Expected: scene.name equals `forest`
   - Expected: scene.object_count() equals `0.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates an empty scene with a name")
val scene = GeneratedScene.new("forest")
expect(scene.name).to_equal("forest")
expect(scene.object_count()).to_equal(0.to_i32())
```

</details>

### add_object

#### adds objects to the scene

- adds objects to the scene
   - Expected: scene.object_count() equals `2.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds objects to the scene")
var scene = GeneratedScene.new("forest")
val obj1 = SceneObject.new("tree", "oak1", 1.0, 2.0)
val obj2 = SceneObject.new("rock", "rock1", 5.0, 6.0)
scene.add_object(obj1)
scene.add_object(obj2)
expect(scene.object_count()).to_equal(2.to_i32())
```

</details>

### to_sdn

#### contains scene name in output

- contains scene name in output


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains scene name in output")
var scene = GeneratedScene.new("forest")
val sdn = scene.to_sdn()
expect(sdn).to_contain("scene: forest")
expect(sdn).to_contain("objects:")
```

</details>

#### serializes objects with type, name, and position

- serializes objects with type, name, and position


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes objects with type, name, and position")
var scene = GeneratedScene.new("village")
var obj = SceneObject.new("house", "house1", 10.0, 20.0)
obj.add_property("roof: red")
scene.add_object(obj)
val sdn = scene.to_sdn()
expect(sdn).to_contain("type: house")
expect(sdn).to_contain("name: house1")
expect(sdn).to_contain("roof: red")
```

</details>

#### serializes multiple objects

- serializes multiple objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes multiple objects")
var scene = GeneratedScene.new("park")
scene.add_object(SceneObject.new("bench", "b1", 0.0, 0.0))
scene.add_object(SceneObject.new("lamp", "l1", 3.0, 4.0))
val sdn = scene.to_sdn()
expect(sdn).to_contain("type: bench")
expect(sdn).to_contain("type: lamp")
```

</details>

### SceneGenerator

### new

#### starts with zero templates

- starts with zero templates
   - Expected: sg.template_count() equals `0.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with zero templates")
val sg = SceneGenerator.new()
expect(sg.template_count()).to_equal(0.to_i32())
```

</details>

### add_template

#### registers a template

- registers a template
   - Expected: sg.template_count() equals `2.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers a template")
var sg = SceneGenerator.new()
sg.add_template("tree")
sg.add_template("player")
expect(sg.template_count()).to_equal(2.to_i32())
```

</details>

### has_template

#### returns true for a registered template

- returns true for a registered template
   - Expected: sg.has_template("tree") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for a registered template")
var sg = SceneGenerator.new()
sg.add_template("tree")
expect(sg.has_template("tree")).to_equal(true)
```

</details>

#### returns false for an unregistered template

- returns false for an unregistered template
   - Expected: sg.has_template("dragon") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for an unregistered template")
val sg = SceneGenerator.new()
expect(sg.has_template("dragon")).to_equal(false)
```

</details>

### generate_from_objects

#### builds a scene from provided objects

- builds a scene from provided objects
   - Expected: scene.name equals `test_scene`
   - Expected: scene.object_count() equals `2.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a scene from provided objects")
val sg = SceneGenerator.new()
val obj1 = SceneObject.new("tree", "t1", 1.0, 2.0)
val obj2 = SceneObject.new("rock", "r1", 3.0, 4.0)
val objects: [SceneObject] = [obj1, obj2]
val scene = sg.generate_from_objects("test_scene", objects)
expect(scene.name).to_equal("test_scene")
expect(scene.object_count()).to_equal(2.to_i32())
```

</details>

#### builds an empty scene from empty list

- builds an empty scene from empty list
   - Expected: scene.object_count() equals `0.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds an empty scene from empty list")
val sg = SceneGenerator.new()
val empty: [SceneObject] = []
val scene = sg.generate_from_objects("empty_scene", empty)
expect(scene.object_count()).to_equal(0.to_i32())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `d481846afd4e4b7568ab1b152176ac8b64fe623a462845833b0761a31220b64f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d481846afd4e4b7568ab1b152176ac8b64fe623a462845833b0761a31220b64f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d481846afd4e4b7568ab1b152176ac8b64fe623a462845833b0761a31220b64f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/engine/scene_generator_spec.spl
mirror: doc/06_spec/unit/lib/engine/scene_generator_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/engine/scene_generator_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/engine/scene_generator_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/engine/scene_generator_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates an object with type, name, and position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/engine/scene_generator_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds a property string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/engine/scene_generator_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates an empty scene with a name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
