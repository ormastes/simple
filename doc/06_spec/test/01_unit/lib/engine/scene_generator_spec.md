# scene_generator_spec

> Scene Generator Tests

<!-- sdn-diagram:id=scene_generator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scene_generator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scene_generator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scene_generator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/lib/engine/scene_generator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Scene Generator Tests

Tests SceneObject construction and properties, GeneratedScene serialization,
and SceneGenerator template management and scene generation.

## Scenarios

### SceneObject

### new

#### creates an object with type, name, and position

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = SceneObject.new("tree", "oak1", 10.0, 20.0)
expect(obj.obj_type).to_equal("tree")
expect(obj.name).to_equal("oak1")
```

</details>

### add_property

#### adds a property string

1. var obj = SceneObject new
2. obj add property
3. obj add property
   - Expected: obj.properties.len().to_i32() equals `2.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var obj = SceneObject.new("tree", "oak1", 5.0, 5.0)
obj.add_property("height: tall")
obj.add_property("color: green")
expect(obj.properties.len().to_i32()).to_equal(2.to_i32())
```

</details>

### GeneratedScene

### new

#### creates an empty scene with a name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scene = GeneratedScene.new("forest")
expect(scene.name).to_equal("forest")
expect(scene.object_count()).to_equal(0.to_i32())
```

</details>

### add_object

#### adds objects to the scene

1. var scene = GeneratedScene new
2. scene add object
3. scene add object
   - Expected: scene.object_count() equals `2.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var scene = GeneratedScene new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scene = GeneratedScene.new("forest")
val sdn = scene.to_sdn()
expect(sdn).to_contain("scene: forest")
expect(sdn).to_contain("objects:")
```

</details>

#### serializes objects with type, name, and position

1. var scene = GeneratedScene new
2. var obj = SceneObject new
3. obj add property
4. scene add object


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var scene = GeneratedScene new
2. scene add object
3. scene add object


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sg = SceneGenerator.new()
expect(sg.template_count()).to_equal(0.to_i32())
```

</details>

### add_template

#### registers a template

1. var sg = SceneGenerator new
2. sg add template
3. sg add template
   - Expected: sg.template_count() equals `2.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sg = SceneGenerator.new()
sg.add_template("tree")
sg.add_template("player")
expect(sg.template_count()).to_equal(2.to_i32())
```

</details>

### has_template

#### returns true for a registered template

1. var sg = SceneGenerator new
2. sg add template
   - Expected: sg.has_template("tree") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sg = SceneGenerator.new()
sg.add_template("tree")
expect(sg.has_template("tree")).to_equal(true)
```

</details>

#### returns false for an unregistered template

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sg = SceneGenerator.new()
expect(sg.has_template("dragon")).to_equal(false)
```

</details>

### generate_from_objects

#### builds a scene from provided objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
