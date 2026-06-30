# Mixin Feature Specification

> Mixins provide a way to compose behavior into classes without using inheritance. They support:

<!-- sdn-diagram:id=mixin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mixin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mixin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mixin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mixin Feature Specification

Mixins provide a way to compose behavior into classes without using inheritance. They support:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/mixin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Mixins provide a way to compose behavior into classes without using inheritance.
They support:
- Field and method composition
- Generic type parameters with inference
- Trait bounds and constraints
- Required methods that targets must implement
- Multiple mixin application

Features not supported by runtime parser:
- mixin keyword
- with keyword for mixin application
- assert keyword (use check() instead)

## Scenarios

### Mixin Declarations

#### Timestamp mixin has correct fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timestamp = MixinTemplate.new("Timestamp", [], ["created_at", "updated_at"], ["touch"], [], [], [])
expect(timestamp.fields.len()).to_equal(2)
expect(contains_text(timestamp.fields, "created_at")).to_equal(true)
expect(contains_text(timestamp.fields, "updated_at")).to_equal(true)
```

</details>

#### Auditable mixin methods compile

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val auditable = MixinTemplate.new("Auditable", [], ["created_at"], ["audit", "history"], [], [], [])
expect(auditable.methods.len()).to_equal(2)
expect(auditable.signature()).to_equal("Auditable")
```

</details>

#### Generic mixin with type parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val generic_box = MixinTemplate.new("Box", ["T"], ["value:TYPE_PARAM"], ["get:TYPE_PARAM"], [], [], [])
val instantiated = generic_box.instantiate("User")
expect(generic_box.signature()).to_equal("Box<T>")
expect(instantiated.type_params.len()).to_equal(0)
expect(instantiated.fields[0]).to_equal("value:User")
```

</details>

### Mixin Application

#### Class can apply mixin

1. var model = ClassModel new
2. model apply mixin
   - Expected: model.has_field("created_at") is true
   - Expected: model.has_method("touch") is true
   - Expected: contains_text(model.mixins, "Timestamp") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timestamp = MixinTemplate.new("Timestamp", [], ["created_at", "updated_at"], ["touch"], [], [], [])
var model = ClassModel.new("Record")
model.apply_mixin(timestamp)
expect(model.has_field("created_at")).to_equal(true)
expect(model.has_method("touch")).to_equal(true)
expect(contains_text(model.mixins, "Timestamp")).to_equal(true)
```

</details>

#### Class can apply multiple mixins

1. var model = ClassModel new
2. model apply mixin
3. model apply mixin
   - Expected: model.fields.len() equals `2`
   - Expected: model.methods.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timestamp = MixinTemplate.new("Timestamp", [], ["created_at"], ["touch"], [], [], [])
val auditable = MixinTemplate.new("Auditable", [], ["updated_by"], ["audit"], [], [], [])
var model = ClassModel.new("Document")
model.apply_mixin(timestamp)
model.apply_mixin(auditable)
expect(model.fields.len()).to_equal(2)
expect(model.methods.len()).to_equal(2)
```

</details>

#### Generic mixin application with concrete type

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = MixinTemplate.new("Box", ["T"], ["value:TYPE_PARAM"], ["get:TYPE_PARAM"], [], [], [])
val concrete = box.instantiate("i64")
expect(concrete.fields[0]).to_equal("value:i64")
expect(concrete.methods[0]).to_equal("get:i64")
```

</details>

### Mixin Constraints

#### Mixin with trait bounds compiles

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpl = MixinTemplate.new("PrintableRecord", [], ["body"], ["print"], ["Printable"], [], [])
expect(tmpl.required_traits.len()).to_equal(1)
expect(contains_text(tmpl.required_traits, "Printable")).to_equal(true)
```

</details>

#### Mixin with required method

1. var model = ClassModel new
2. model apply mixin
   - Expected: model.can_satisfy_required_methods() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpl = MixinTemplate.new("Renderable", [], ["title"], ["render"], [], ["render"], [])
var model = ClassModel.new("Card")
model.required_methods = ["render"]
model.apply_mixin(tmpl)
expect(model.can_satisfy_required_methods()).to_equal(true)
```

</details>

### Mixin Field and Method Access

#### Class method accesses mixin field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_value_field("text")).to_equal("value:text")
expect(type_inference_from_mixin("value:text", "value:")).to_equal(true)
```

</details>

#### Class method calls mixin method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_audit_message("create")).to_equal("audit:create")
expect(render_audit_message("delete")).to_equal("audit:delete")
```

</details>

### Mixin Type Inference

#### Type inference with mixins

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpl = MixinTemplate.new("Box", ["T"], ["value:TYPE_PARAM"], ["get:TYPE_PARAM"], [], [], [])
val instantiated = tmpl.instantiate("User")
expect(type_inference_from_mixin(instantiated.fields[0], "value:")).to_equal(true)
expect(instantiated.fields[0]).to_equal("value:User")
```

</details>

### Mixin Composition

#### Mixin composition

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val address = MixinTemplate.new("Address", [], ["street"], ["format_address"], [], [], ["Geo"])
val contact = MixinTemplate.new("Contact", [], ["email"], ["format_contact"], [], [], ["Address"])
val geo = MixinTemplate.new("Geo", [], ["lat", "lon"], ["format_geo"], [], [], [])
val resolver = MixinResolver.new([address, contact, geo])
val resolved = resolver.resolve_transitive(["Contact"])
expect(resolved[0]).to_equal("Contact")
expect(resolved[1]).to_equal("Address")
expect(resolved[2]).to_equal("Geo")
```

</details>

### Mixin Conflict Detection

#### Field conflict is detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(field_conflict_detected(["id", "name", "id"])).to_equal(true)
expect(field_conflict_detected(["id", "name"])).to_equal(false)
```

</details>

#### Method conflict is detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(method_conflict_detected(["draw", "paint", "draw"])).to_equal(true)
expect(method_conflict_detected(["draw", "paint"])).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
