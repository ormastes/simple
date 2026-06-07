# Types Specification

> <details>

<!-- sdn-diagram:id=types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

types_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 90 | 90 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Types Specification

## Scenarios

### CapsuleVisibility

#### Public is_public returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vis = CapsuleVisibility.Public
expect(vis.is_public()).to_equal(true)
```

</details>

#### Public is_internal returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vis = CapsuleVisibility.Public
expect(vis.is_internal()).to_equal(false)
```

</details>

#### Public is_private returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vis = CapsuleVisibility.Public
expect(vis.is_private()).to_equal(false)
```

</details>

#### Internal is_internal returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vis = CapsuleVisibility.Internal
expect(vis.is_internal()).to_equal(true)
```

</details>

#### Internal is_public returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vis = CapsuleVisibility.Internal
expect(vis.is_public()).to_equal(false)
```

</details>

#### Private is_private returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vis = CapsuleVisibility.Private
expect(vis.is_private()).to_equal(true)
```

</details>

#### Private is_public returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vis = CapsuleVisibility.Private
expect(vis.is_public()).to_equal(false)
```

</details>

#### Private is_internal returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vis = CapsuleVisibility.Private
expect(vis.is_internal()).to_equal(false)
```

</details>

#### Public to_text returns public

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CapsuleVisibility.Public.to_text()).to_equal("public")
```

</details>

#### Internal to_text returns internal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CapsuleVisibility.Internal.to_text()).to_equal("internal")
```

</details>

#### Private to_text returns private

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CapsuleVisibility.Private.to_text()).to_equal("private")
```

</details>

### CaretId

#### constructs with name and path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caret = CaretId.new("core", "src/core")
expect(caret.name).to_equal("core")
expect(caret.path).to_equal("src/core")
expect(caret.is_default).to_equal(false)
```

</details>

#### default_caret uses name main

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caret = CaretId.default_caret("src/")
expect(caret.name).to_equal("main")
expect(caret.path).to_equal("src/")
expect(caret.is_default).to_equal(true)
```

</details>

#### caret_prefix prepends caret symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caret = CaretId.new("ui", "src/ui")
expect(caret.caret_prefix()).to_equal("^ui")
```

</details>

#### default caret prefix is ^main

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caret = CaretId.default_caret("src/")
expect(caret.caret_prefix()).to_equal("^main")
```

</details>

#### equals compares by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = CaretId.new("core", "src/core")
val b = CaretId.new("core", "other/path")
expect(a.equals(b)).to_equal(true)
```

</details>

#### equals returns false for different names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = CaretId.new("core", "src/core")
val b = CaretId.new("ui", "src/ui")
expect(a.equals(b)).to_equal(false)
```

</details>

### CaretMapping

#### constructs with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapping = CaretMapping.new("core", "feature/auth/**", "feature/auth")
expect(mapping.caret_name).to_equal("core")
expect(mapping.match_pattern).to_equal("feature/auth/**")
expect(mapping.target_key).to_equal("feature/auth")
```

</details>

#### matches_path with glob wildcard

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapping = CaretMapping.new("core", "feature/auth/**", "feature/auth")
expect(mapping.matches_path("feature/auth/login.spl")).to_equal(true)
expect(mapping.matches_path("feature/auth/register/form.spl")).to_equal(true)
```

</details>

#### matches_path rejects non-matching paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapping = CaretMapping.new("core", "feature/auth/**", "feature/auth")
expect(mapping.matches_path("feature/billing/pay.spl")).to_equal(false)
```

</details>

#### matches_path with exact match (no glob)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapping = CaretMapping.new("core", "feature/auth", "feature/auth")
expect(mapping.matches_path("feature/auth")).to_equal(true)
expect(mapping.matches_path("feature/auth/sub")).to_equal(false)
```

</details>

#### matches_path base prefix includes slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapping = CaretMapping.new("ui", "ui_feature/auth/**", "feature/auth")
expect(mapping.matches_path("ui_feature/auth/view.spl")).to_equal(true)
expect(mapping.matches_path("ui_feature/billing/view.spl")).to_equal(false)
```

</details>

### LayerDirection

#### UpperToLower to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = LayerDirection.UpperToLower
expect(dir.to_text()).to_equal("upper_to_lower")
```

</details>

#### LowerToUpper to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = LayerDirection.LowerToUpper
expect(dir.to_text()).to_equal("lower_to_upper")
```

</details>

### LayerDef

#### empty creates no layers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.empty()
expect(layer.order.len()).to_equal(0)
expect(layer.allow_same_layer).to_equal(true)
expect(layer.allow_adjacent_only).to_equal(false)
```

</details>

#### new creates with order and direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val order = ["api", "app", "domain", "infra"]
val layer = LayerDef.new(order, LayerDirection.UpperToLower)
expect(layer.order.len()).to_equal(4)
expect(layer.allow_same_layer).to_equal(true)
```

</details>

#### get_level returns correct index

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.UpperToLower)
expect(layer.get_level("api")).to_equal(0)
expect(layer.get_level("app")).to_equal(1)
expect(layer.get_level("domain")).to_equal(2)
expect(layer.get_level("infra")).to_equal(3)
```

</details>

#### get_level returns -1 for unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
expect(layer.get_level("unknown")).to_equal(-1)
```

</details>

#### has_layer returns true for known layers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain"], LayerDirection.UpperToLower)
expect(layer.has_layer("api")).to_equal(true)
expect(layer.has_layer("domain")).to_equal(true)
```

</details>

#### has_layer returns false for unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
expect(layer.has_layer("infra")).to_equal(false)
```

</details>

#### layer_count returns length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain"], LayerDirection.UpperToLower)
expect(layer.layer_count()).to_equal(3)
```

</details>

#### empty layer_count is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.empty()
expect(layer.layer_count()).to_equal(0)
```

</details>

### LayerDef can_depend UpperToLower

#### allows upper to depend on lower

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.UpperToLower)
# api (0) -> app (1): upper depends on lower = allowed
expect(layer.can_depend("api", "app")).to_equal(true)
# api (0) -> infra (3): upper depends on lower = allowed
expect(layer.can_depend("api", "infra")).to_equal(true)
```

</details>

#### denies lower depending on upper

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.UpperToLower)
# infra (3) -> api (0): lower depends on upper = denied
expect(layer.can_depend("infra", "api")).to_equal(false)
# domain (2) -> app (1): lower depends on upper = denied
expect(layer.can_depend("domain", "app")).to_equal(false)
```

</details>

#### allows same layer by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
expect(layer.can_depend("app", "app")).to_equal(true)
```

</details>

#### denies same layer when disabled

1. var layer = LayerDef new
   - Expected: layer.can_depend("app", "app") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
layer.allow_same_layer = false
expect(layer.can_depend("app", "app")).to_equal(false)
```

</details>

#### allows unknown layers (no restriction)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
# unknown -> api: unrestricted
expect(layer.can_depend("unknown", "api")).to_equal(true)
# api -> unknown: unrestricted
expect(layer.can_depend("api", "unknown")).to_equal(true)
```

</details>

### LayerDef can_depend LowerToUpper

#### allows lower to depend on upper

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.LowerToUpper)
# infra (3) -> api (0): lower depends on upper = allowed
expect(layer.can_depend("infra", "api")).to_equal(true)
# domain (2) -> app (1): lower depends on upper = allowed
expect(layer.can_depend("domain", "app")).to_equal(true)
```

</details>

#### denies upper depending on lower

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.LowerToUpper)
# api (0) -> infra (3): upper depends on lower = denied
expect(layer.can_depend("api", "infra")).to_equal(false)
```

</details>

### LayerDef adjacent_only mode

#### allows adjacent layers only (UpperToLower)

1. var layer = LayerDef new
   - Expected: layer.can_depend("api", "app") is true
   - Expected: layer.can_depend("api", "domain") is false
   - Expected: layer.can_depend("api", "infra") is false
   - Expected: layer.can_depend("app", "domain") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.UpperToLower)
layer.allow_adjacent_only = true
# api (0) -> app (1): adjacent = allowed
expect(layer.can_depend("api", "app")).to_equal(true)
# api (0) -> domain (2): skip = denied
expect(layer.can_depend("api", "domain")).to_equal(false)
# api (0) -> infra (3): skip = denied
expect(layer.can_depend("api", "infra")).to_equal(false)
# app (1) -> domain (2): adjacent = allowed
expect(layer.can_depend("app", "domain")).to_equal(true)
```

</details>

#### allows adjacent layers only (LowerToUpper)

1. var layer = LayerDef new
   - Expected: layer.can_depend("infra", "domain") is true
   - Expected: layer.can_depend("infra", "api") is false
   - Expected: layer.can_depend("domain", "app") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.LowerToUpper)
layer.allow_adjacent_only = true
# infra (3) -> domain (2): adjacent = allowed
expect(layer.can_depend("infra", "domain")).to_equal(true)
# infra (3) -> api (0): skip = denied
expect(layer.can_depend("infra", "api")).to_equal(false)
# domain (2) -> app (1): adjacent = allowed
expect(layer.can_depend("domain", "app")).to_equal(true)
```

</details>

### LayerDef describe_violation

#### describes same-layer violation

1. var layer = LayerDef new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
layer.allow_same_layer = false
val msg = layer.describe_violation("app", "app")
expect(msg).to_contain("same-layer dependency")
expect(msg).to_contain("app")
```

</details>

#### describes cross-layer violation with levels

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.UpperToLower)
val msg = layer.describe_violation("infra", "api")
expect(msg).to_contain("infra")
expect(msg).to_contain("api")
expect(msg).to_contain("level")
```

</details>

### VirtualCapsule

#### constructs with name, dimension, layer

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = VirtualCapsule.new("auth", "feature", "domain")
expect(cap.name).to_equal("auth")
expect(cap.dimension).to_equal("feature")
expect(cap.layer).to_equal("domain")
expect(cap.bindings.len()).to_equal(0)
expect(cap.exports.len()).to_equal(0)
```

</details>

#### capsule_id returns dimension/name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = VirtualCapsule.new("auth", "feature", "domain")
expect(cap.capsule_id()).to_equal("feature/auth")
```

</details>

#### capsule_id for platform dimension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = VirtualCapsule.new("linux", "platform", "infra")
expect(cap.capsule_id()).to_equal("platform/linux")
```

</details>

### VirtualCapsule bindings

#### find_binding returns nil for empty capsule

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = VirtualCapsule.new("auth", "feature", "domain")
val result = cap.find_binding("core_auth")
expect(result).to_be_nil()
```

</details>

#### find_binding returns matching binding

1. var cap = VirtualCapsule new
2. cap bindings = [SurfaceBinding new
   - Expected: binding.alias equals `core_auth`
   - Expected: binding.source_caret equals `core`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cap = VirtualCapsule.new("auth", "feature", "domain")
cap.bindings = [SurfaceBinding.new("core", "feature/auth/login.spl", "core_auth")]
val result = cap.find_binding("core_auth")
expect(result).to_be(result)
val binding = result ?? SurfaceBinding.new("", "", "")
expect(binding.alias).to_equal("core_auth")
expect(binding.source_caret).to_equal("core")
```

</details>

#### find_binding returns nil for no match

1. var cap = VirtualCapsule new
2. cap bindings = [SurfaceBinding new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cap = VirtualCapsule.new("auth", "feature", "domain")
cap.bindings = [SurfaceBinding.new("core", "feature/auth/login.spl", "core_auth")]
val result = cap.find_binding("ui_auth")
expect(result).to_be_nil()
```

</details>

#### has_binding_from returns true when caret present

1. var cap = VirtualCapsule new
2. cap bindings = [SurfaceBinding new
   - Expected: cap.has_binding_from("core") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cap = VirtualCapsule.new("auth", "feature", "domain")
cap.bindings = [SurfaceBinding.new("core", "feature/auth/login.spl", "core_auth")]
expect(cap.has_binding_from("core")).to_equal(true)
```

</details>

#### has_binding_from returns false when caret absent

1. var cap = VirtualCapsule new
2. cap bindings = [SurfaceBinding new
   - Expected: cap.has_binding_from("ui") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cap = VirtualCapsule.new("auth", "feature", "domain")
cap.bindings = [SurfaceBinding.new("core", "feature/auth/login.spl", "core_auth")]
expect(cap.has_binding_from("ui")).to_equal(false)
```

</details>

### VirtualCapsule exports

#### find_export returns nil for empty capsule

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = VirtualCapsule.new("auth", "feature", "domain")
val result = cap.find_export("login")
expect(result).to_be_nil()
```

</details>

#### find_export returns matching export

1. var cap = VirtualCapsule new
2. cap exports = [CapsuleExport public export
   - Expected: exp.symbol_name equals `login`
   - Expected: exp.binding_alias equals `core_auth`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cap = VirtualCapsule.new("auth", "feature", "domain")
cap.exports = [CapsuleExport.public_export("core_auth", "login")]
val result = cap.find_export("login")
val exp = result ?? CapsuleExport.public_export("", "")
expect(exp.symbol_name).to_equal("login")
expect(exp.binding_alias).to_equal("core_auth")
```

</details>

#### public_exports filters public only

1. var cap = VirtualCapsule new
2. CapsuleExport public export
3. CapsuleExport internal export
4. CapsuleExport public export
   - Expected: pub_list.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cap = VirtualCapsule.new("auth", "feature", "domain")
cap.exports = [
    CapsuleExport.public_export("a", "login"),
    CapsuleExport.internal_export("b", "helper"),
    CapsuleExport.public_export("c", "logout")
]
val pub_list = cap.public_exports()
expect(pub_list.len()).to_equal(2)
```

</details>

#### internal_exports filters internal only

1. var cap = VirtualCapsule new
2. CapsuleExport public export
3. CapsuleExport internal export
4. CapsuleExport internal export
   - Expected: int_exports.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cap = VirtualCapsule.new("auth", "feature", "domain")
cap.exports = [
    CapsuleExport.public_export("a", "login"),
    CapsuleExport.internal_export("b", "helper"),
    CapsuleExport.internal_export("c", "utils")
]
val int_exports = cap.internal_exports()
expect(int_exports.len()).to_equal(2)
```

</details>

### SurfaceBinding

#### constructs with caret, path, alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = SurfaceBinding.new("core", "feature/auth/login.spl", "core_auth")
expect(binding.source_caret).to_equal("core")
expect(binding.source_path).to_equal("feature/auth/login.spl")
expect(binding.alias).to_equal("core_auth")
```

</details>

#### different bindings have different aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = SurfaceBinding.new("core", "auth.spl", "core_auth")
val b = SurfaceBinding.new("ui", "auth.spl", "ui_auth")
expect(a.alias).to_equal("core_auth")
expect(b.alias).to_equal("ui_auth")
expect(a.source_caret).to_equal("core")
expect(b.source_caret).to_equal("ui")
```

</details>

### CapsuleExport

#### public_export creates Public visibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exp = CapsuleExport.public_export("core_auth", "login")
expect(exp.visibility.is_public()).to_equal(true)
expect(exp.binding_alias).to_equal("core_auth")
expect(exp.symbol_name).to_equal("login")
```

</details>

#### internal_export creates Internal visibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exp = CapsuleExport.internal_export("core_auth", "helper")
expect(exp.visibility.is_internal()).to_equal(true)
```

</details>

#### qualified_name joins alias and symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exp = CapsuleExport.public_export("core_auth", "login")
expect(exp.qualified_name()).to_equal("core_auth.login")
```

</details>

#### is_accessible_from_capsule for Public

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exp = CapsuleExport.public_export("a", "sym")
expect(exp.is_accessible_from_capsule()).to_equal(true)
```

</details>

#### is_accessible_from_capsule for Internal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exp = CapsuleExport.internal_export("a", "sym")
expect(exp.is_accessible_from_capsule()).to_equal(true)
```

</details>

#### is_accessible_from_capsule for Private

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exp = CapsuleExport.private_export("a", "sym")
expect(exp.is_accessible_from_capsule()).to_equal(false)
```

</details>

### BypassGrant

#### constructs with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grant = BypassGrant.new(
    "infra/db",
    "raw_query",
    "domain->infra",
    "performance critical",
    "infra/db.spl:10"
)
expect(grant.granting_module).to_equal("infra/db")
expect(grant.granted_symbol).to_equal("raw_query")
expect(grant.layer_edge).to_equal("domain->infra")
expect(grant.reason).to_equal("performance critical")
expect(grant.location).to_equal("infra/db.spl:10")
```

</details>

#### grant_key joins module and symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grant = BypassGrant.new(
    "infra/db",
    "raw_query",
    "domain->infra",
    "perf",
    "db.spl:10"
)
expect(grant.grant_key()).to_equal("infra/db::raw_query")
```

</details>

#### grant_key is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = BypassGrant.new("mod", "sym", "e", "r", "l")
val b = BypassGrant.new("mod", "sym", "e2", "r2", "l2")
expect(a.grant_key()).to_equal(b.grant_key())
```

</details>

### CapsuleRules

#### strict enables all enforcement

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = CapsuleRules.strict()
expect(rules.enforce_layering).to_equal(true)
expect(rules.reject_cycles).to_equal(true)
expect(rules.forbid_implicit_merge).to_equal(true)
expect(rules.require_explicit_bind).to_equal(true)
```

</details>

#### permissive disables all enforcement

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = CapsuleRules.permissive()
expect(rules.enforce_layering).to_equal(false)
expect(rules.reject_cycles).to_equal(false)
expect(rules.forbid_implicit_merge).to_equal(false)
expect(rules.require_explicit_bind).to_equal(false)
```

</details>

#### default_rules returns strict

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = CapsuleRules.default_rules()
expect(rules.enforce_layering).to_equal(true)
expect(rules.reject_cycles).to_equal(true)
expect(rules.forbid_implicit_merge).to_equal(true)
expect(rules.require_explicit_bind).to_equal(true)
```

</details>

### MdsocManifest

#### constructs with name and defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = MdsocManifest.new("my-project")
expect(manifest.name).to_equal("my-project")
expect(manifest.version).to_equal("0.1.0")
expect(manifest.carets.len()).to_equal(0)
expect(manifest.dimensions.len()).to_equal(0)
expect(manifest.capsules.len()).to_equal(0)
expect(manifest.bypass_grants.len()).to_equal(0)
# default rules are strict
expect(manifest.rules.enforce_layering).to_equal(true)
```

</details>

#### get_caret returns nil when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = MdsocManifest.new("proj")
val result = manifest.get_caret("core")
expect(result).to_be_nil()
```

</details>

#### get_caret returns matching caret

1. var manifest = MdsocManifest new
2. manifest carets = [CaretId new
   - Expected: caret.name equals `ui`
   - Expected: caret.path equals `src/ui`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = MdsocManifest.new("proj")
manifest.carets = [CaretId.new("core", "src/core"), CaretId.new("ui", "src/ui")]
val result = manifest.get_caret("ui")
val caret = result ?? CaretId.default_caret("")
expect(caret.name).to_equal("ui")
expect(caret.path).to_equal("src/ui")
```

</details>

#### get_caret returns nil for non-existent

1. var manifest = MdsocManifest new
2. manifest carets = [CaretId new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = MdsocManifest.new("proj")
manifest.carets = [CaretId.new("core", "src/core")]
val result = manifest.get_caret("infra")
expect(result).to_be_nil()
```

</details>

#### get_dimension returns matching dimension

1. var manifest = MdsocManifest new
2. manifest dimensions = [DimensionDef new
   - Expected: dim.name equals `feature`
   - Expected: dim.key_template equals `feature/" + r"{name}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = MdsocManifest.new("proj")
manifest.dimensions = [DimensionDef.new("feature", "feature/" + r"{name}")]
val result = manifest.get_dimension("feature")
val dim = result ?? DimensionDef.new("", "")
expect(dim.name).to_equal("feature")
expect(dim.key_template).to_equal("feature/" + r"{name}")
```

</details>

#### get_dimension returns nil for non-existent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = MdsocManifest.new("proj")
val result = manifest.get_dimension("platform")
expect(result).to_be_nil()
```

</details>

#### get_capsule returns matching capsule

1. var manifest = MdsocManifest new
2. manifest capsules = [VirtualCapsule new
   - Expected: cap.name equals `auth`
   - Expected: cap.dimension equals `feature`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = MdsocManifest.new("proj")
manifest.capsules = [VirtualCapsule.new("auth", "feature", "domain")]
val result = manifest.get_capsule("auth")
val cap = result ?? VirtualCapsule.new("", "", "")
expect(cap.name).to_equal("auth")
expect(cap.dimension).to_equal("feature")
```

</details>

#### get_capsule returns nil for non-existent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = MdsocManifest.new("proj")
val result = manifest.get_capsule("billing")
expect(result).to_be_nil()
```

</details>

#### find_bypass_grant returns matching grant

1. var manifest = MdsocManifest new
2. manifest bypass grants = [BypassGrant new
   - Expected: grant.granted_symbol equals `raw_query`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = MdsocManifest.new("proj")
manifest.bypass_grants = [BypassGrant.new("mod", "raw_query", "e", "r", "l")]
val result = manifest.find_bypass_grant("raw_query")
val grant = result ?? BypassGrant.new("", "", "", "", "")
expect(grant.granted_symbol).to_equal("raw_query")
```

</details>

#### find_bypass_grant returns nil for no match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = MdsocManifest.new("proj")
val result = manifest.find_bypass_grant("nonexistent")
expect(result).to_be_nil()
```

</details>

#### find_capsule_by_id matches dimension/name

1. var manifest = MdsocManifest new
2. manifest capsules = [VirtualCapsule new
   - Expected: cap.name equals `auth`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = MdsocManifest.new("proj")
manifest.capsules = [VirtualCapsule.new("auth", "feature", "domain")]
val result = manifest.find_capsule_by_id("feature/auth")
val cap = result ?? VirtualCapsule.new("", "", "")
expect(cap.name).to_equal("auth")
```

</details>

#### find_capsule_by_id returns nil for wrong id

1. var manifest = MdsocManifest new
2. manifest capsules = [VirtualCapsule new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = MdsocManifest.new("proj")
manifest.capsules = [VirtualCapsule.new("auth", "feature", "domain")]
val result = manifest.find_capsule_by_id("platform/auth")
expect(result).to_be_nil()
```

</details>

### DimensionDef

#### new sets defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dim = DimensionDef.new("feature", "feature/" + r"{name}")
expect(dim.name).to_equal("feature")
expect(dim.key_template).to_equal("feature/" + r"{name}")
expect(dim.surface_file).to_equal("__init__.spl")
expect(dim.participation).to_equal("explicit_bind_only")
expect(dim.intra_access).to_equal("via_surface_only")
expect(dim.symbol_merge).to_equal("forbid_implicit")
expect(dim.dep_cycles).to_equal("reject")
expect(dim.mappings.len()).to_equal(0)
```

</details>

#### expand_key substitutes name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dim = DimensionDef.new("feature", "feature/" + r"{name}")
expect(dim.expand_key("auth")).to_equal("feature/auth")
expect(dim.expand_key("billing")).to_equal("feature/billing")
```

</details>

#### expand_key with nested template

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dim = DimensionDef.new("platform", "platform/" + r"{name}" + "/driver")
expect(dim.expand_key("linux")).to_equal("platform/linux/driver")
```

</details>

#### is_explicit_bind returns true for default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dim = DimensionDef.new("feature", "feature/" + r"{name}")
expect(dim.is_explicit_bind()).to_equal(true)
```

</details>

#### is_explicit_bind returns false for other participation

1. var dim = DimensionDef new
   - Expected: dim.is_explicit_bind() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dim = DimensionDef.new("feature", "feature/" + r"{name}")
dim.participation = "auto_bind"
expect(dim.is_explicit_bind()).to_equal(false)
```

</details>

#### rejects_cycles returns true for default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dim = DimensionDef.new("feature", "feature/" + r"{name}")
expect(dim.rejects_cycles()).to_equal(true)
```

</details>

#### rejects_cycles returns false for allow

1. var dim = DimensionDef new
   - Expected: dim.rejects_cycles() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dim = DimensionDef.new("feature", "feature/" + r"{name}")
dim.dep_cycles = "allow"
expect(dim.rejects_cycles()).to_equal(false)
```

</details>

#### find_mapping returns matching mapping

1. var dim = DimensionDef new
2. CaretMapping new
3. CaretMapping new
   - Expected: mapping.caret_name equals `ui`
   - Expected: mapping.match_pattern equals `ui_feature/**`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dim = DimensionDef.new("feature", "feature/" + r"{name}")
dim.mappings = [
    CaretMapping.new("core", "feature/**", "feature"),
    CaretMapping.new("ui", "ui_feature/**", "feature")
]
val result = dim.find_mapping("ui")
val mapping = result ?? CaretMapping.new("", "", "")
expect(mapping.caret_name).to_equal("ui")
expect(mapping.match_pattern).to_equal("ui_feature/**")
```

</details>

#### find_mapping returns nil for no match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dim = DimensionDef.new("feature", "feature/" + r"{name}")
val result = dim.find_mapping("unknown")
expect(result).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mdsoc/types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CapsuleVisibility
- CaretId
- CaretMapping
- LayerDirection
- LayerDef
- LayerDef can_depend UpperToLower
- LayerDef can_depend LowerToUpper
- LayerDef adjacent_only mode
- LayerDef describe_violation
- VirtualCapsule
- VirtualCapsule bindings
- VirtualCapsule exports
- SurfaceBinding
- CapsuleExport
- BypassGrant
- CapsuleRules
- MdsocManifest
- DimensionDef

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 90 |
| Active scenarios | 90 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
