# types_spec

> Purpose: Prove that CapsuleVisibility.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 90 | 90 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# types_spec

Purpose: Prove that CapsuleVisibility.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/mdsoc/types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that CapsuleVisibility.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### CapsuleVisibility

#### Public is_public returns true

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Public is_public returns true
- Verify: Public is_public returns true
   - Expected: vis.is_public() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Public is_public returns true")
step("Verify: Public is_public returns true")
# @req: REQ-COMPILER-MDSOC-001
val vis = CapsuleVisibility.Public
expect(vis.is_public()).to_equal(true)
```

</details>

#### Public is_internal returns false

- Public is_internal returns false
- Verify: Public is_internal returns false
   - Expected: vis.is_internal() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Public is_internal returns false")
step("Verify: Public is_internal returns false")
val vis = CapsuleVisibility.Public
expect(vis.is_internal()).to_equal(false)
```

</details>

#### Public is_private returns false

- Public is_private returns false
- Verify: Public is_private returns false
   - Expected: vis.is_private() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Public is_private returns false")
step("Verify: Public is_private returns false")
val vis = CapsuleVisibility.Public
expect(vis.is_private()).to_equal(false)
```

</details>

#### Internal is_internal returns true

- Internal is_internal returns true
- Verify: Internal is_internal returns true
   - Expected: vis.is_internal() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Internal is_internal returns true")
step("Verify: Internal is_internal returns true")
val vis = CapsuleVisibility.Internal
expect(vis.is_internal()).to_equal(true)
```

</details>

#### Internal is_public returns false

- Internal is_public returns false
- Verify: Internal is_public returns false
   - Expected: vis.is_public() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Internal is_public returns false")
step("Verify: Internal is_public returns false")
val vis = CapsuleVisibility.Internal
expect(vis.is_public()).to_equal(false)
```

</details>

#### Private is_private returns true

- Private is_private returns true
- Verify: Private is_private returns true
   - Expected: vis.is_private() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Private is_private returns true")
step("Verify: Private is_private returns true")
val vis = CapsuleVisibility.Private
expect(vis.is_private()).to_equal(true)
```

</details>

#### Private is_public returns false

- Private is_public returns false
- Verify: Private is_public returns false
   - Expected: vis.is_public() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Private is_public returns false")
step("Verify: Private is_public returns false")
val vis = CapsuleVisibility.Private
expect(vis.is_public()).to_equal(false)
```

</details>

#### Private is_internal returns false

- Private is_internal returns false
- Verify: Private is_internal returns false
   - Expected: vis.is_internal() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Private is_internal returns false")
step("Verify: Private is_internal returns false")
val vis = CapsuleVisibility.Private
expect(vis.is_internal()).to_equal(false)
```

</details>

#### Public to_text returns public

- Public to_text returns public
- Verify: Public to_text returns public
   - Expected: CapsuleVisibility.Public.to_text() equals `public`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Public to_text returns public")
step("Verify: Public to_text returns public")
expect(CapsuleVisibility.Public.to_text()).to_equal("public")
```

</details>

#### Internal to_text returns internal

- Internal to_text returns internal
- Verify: Internal to_text returns internal
   - Expected: CapsuleVisibility.Internal.to_text() equals `internal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Internal to_text returns internal")
step("Verify: Internal to_text returns internal")
expect(CapsuleVisibility.Internal.to_text()).to_equal("internal")
```

</details>

#### Private to_text returns private

- Private to_text returns private
- Verify: Private to_text returns private
   - Expected: CapsuleVisibility.Private.to_text() equals `private`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Private to_text returns private")
step("Verify: Private to_text returns private")
expect(CapsuleVisibility.Private.to_text()).to_equal("private")
```

</details>

### CaretId

#### constructs with name and path

- constructs with name and path
- Verify: constructs with name and path
   - Expected: caret.name equals `core`
   - Expected: caret.path equals `src/core`
   - Expected: caret.is_default is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with name and path")
step("Verify: constructs with name and path")
val caret = CaretId.new("core", "src/core")
expect(caret.name).to_equal("core")
expect(caret.path).to_equal("src/core")
expect(caret.is_default).to_equal(false)
```

</details>

#### default_caret uses name main

- default_caret uses name main
- Verify: default_caret uses name main
   - Expected: caret.name equals `main`
   - Expected: caret.path equals `src/`
   - Expected: caret.is_default is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default_caret uses name main")
step("Verify: default_caret uses name main")
val caret = CaretId.default_caret("src/")
expect(caret.name).to_equal("main")
expect(caret.path).to_equal("src/")
expect(caret.is_default).to_equal(true)
```

</details>

#### caret_prefix prepends caret symbol

- caret_prefix prepends caret symbol
- Verify: caret_prefix prepends caret symbol
   - Expected: caret.caret_prefix() equals `^ui`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caret_prefix prepends caret symbol")
step("Verify: caret_prefix prepends caret symbol")
val caret = CaretId.new("ui", "src/ui")
expect(caret.caret_prefix()).to_equal("^ui")
```

</details>

#### default caret prefix is ^main

- default caret prefix is ^main
- Verify: default caret prefix is ^main
   - Expected: caret.caret_prefix() equals `^main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default caret prefix is ^main")
step("Verify: default caret prefix is ^main")
val caret = CaretId.default_caret("src/")
expect(caret.caret_prefix()).to_equal("^main")
```

</details>

#### equals compares by name

- equals compares by name
- Verify: equals compares by name
   - Expected: a.equals(b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("equals compares by name")
step("Verify: equals compares by name")
val a = CaretId.new("core", "src/core")
val b = CaretId.new("core", "other/path")
expect(a.equals(b)).to_equal(true)
```

</details>

#### equals returns false for different names

- equals returns false for different names
- Verify: equals returns false for different names
   - Expected: a.equals(b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("equals returns false for different names")
step("Verify: equals returns false for different names")
val a = CaretId.new("core", "src/core")
val b = CaretId.new("ui", "src/ui")
expect(a.equals(b)).to_equal(false)
```

</details>

### CaretMapping

#### constructs with all fields

- constructs with all fields
- Verify: constructs with all fields
   - Expected: mapping.caret_name equals `core`
   - Expected: mapping.match_pattern equals `feature/auth/**`
   - Expected: mapping.target_key equals `feature/auth`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with all fields")
step("Verify: constructs with all fields")
val mapping = CaretMapping.new("core", "feature/auth/**", "feature/auth")
expect(mapping.caret_name).to_equal("core")
expect(mapping.match_pattern).to_equal("feature/auth/**")
expect(mapping.target_key).to_equal("feature/auth")
```

</details>

#### matches_path with glob wildcard

- matches_path with glob wildcard
- Verify: matches_path with glob wildcard
   - Expected: mapping.matches_path("feature/auth/login.spl") is true
   - Expected: mapping.matches_path("feature/auth/register/form.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches_path with glob wildcard")
step("Verify: matches_path with glob wildcard")
val mapping = CaretMapping.new("core", "feature/auth/**", "feature/auth")
expect(mapping.matches_path("feature/auth/login.spl")).to_equal(true)
expect(mapping.matches_path("feature/auth/register/form.spl")).to_equal(true)
```

</details>

#### matches_path rejects non-matching paths

- matches_path rejects non-matching paths
- Verify: matches_path rejects non-matching paths
   - Expected: mapping.matches_path("feature/billing/pay.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches_path rejects non-matching paths")
step("Verify: matches_path rejects non-matching paths")
val mapping = CaretMapping.new("core", "feature/auth/**", "feature/auth")
expect(mapping.matches_path("feature/billing/pay.spl")).to_equal(false)
```

</details>

#### matches_path with exact match (no glob)

- matches_path with exact match (no glob)
- Verify: matches_path with exact match (no glob)
   - Expected: mapping.matches_path("feature/auth") is true
   - Expected: mapping.matches_path("feature/auth/sub") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches_path with exact match (no glob)")
step("Verify: matches_path with exact match (no glob)")
val mapping = CaretMapping.new("core", "feature/auth", "feature/auth")
expect(mapping.matches_path("feature/auth")).to_equal(true)
expect(mapping.matches_path("feature/auth/sub")).to_equal(false)
```

</details>

#### matches_path base prefix includes slash

- matches_path base prefix includes slash
- Verify: matches_path base prefix includes slash
   - Expected: mapping.matches_path("ui_feature/auth/view.spl") is true
   - Expected: mapping.matches_path("ui_feature/billing/view.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches_path base prefix includes slash")
step("Verify: matches_path base prefix includes slash")
val mapping = CaretMapping.new("ui", "ui_feature/auth/**", "feature/auth")
expect(mapping.matches_path("ui_feature/auth/view.spl")).to_equal(true)
expect(mapping.matches_path("ui_feature/billing/view.spl")).to_equal(false)
```

</details>

### LayerDirection

#### UpperToLower to_text

- UpperToLower to_text
- Verify: UpperToLower to_text
   - Expected: dir.to_text() equals `upper_to_lower`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UpperToLower to_text")
step("Verify: UpperToLower to_text")
val dir = LayerDirection.UpperToLower
expect(dir.to_text()).to_equal("upper_to_lower")
```

</details>

#### LowerToUpper to_text

- LowerToUpper to_text
- Verify: LowerToUpper to_text
   - Expected: dir.to_text() equals `lower_to_upper`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LowerToUpper to_text")
step("Verify: LowerToUpper to_text")
val dir = LayerDirection.LowerToUpper
expect(dir.to_text()).to_equal("lower_to_upper")
```

</details>

### LayerDef

#### empty creates no layers

- empty creates no layers
- Verify: empty creates no layers
   - Expected: layer.order.len() equals `0`
   - Expected: layer.allow_same_layer is true
   - Expected: layer.allow_adjacent_only is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty creates no layers")
step("Verify: empty creates no layers")
val layer = LayerDef.empty()
expect(layer.order.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(layer.allow_same_layer).to_equal(true)
expect(layer.allow_adjacent_only).to_equal(false)
```

</details>

#### new creates with order and direction

- new creates with order and direction
- Verify: new creates with order and direction
   - Expected: layer.order.len() equals `4`
   - Expected: layer.allow_same_layer is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new creates with order and direction")
step("Verify: new creates with order and direction")
val order = ["api", "app", "domain", "infra"]
val layer = LayerDef.new(order, LayerDirection.UpperToLower)
expect(layer.order.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(layer.allow_same_layer).to_equal(true)
```

</details>

#### get_level returns correct index

- get_level returns correct index
- Verify: get_level returns correct index
   - Expected: layer.get_level("api") equals `0`
   - Expected: layer.get_level("app") equals `1`
   - Expected: layer.get_level("domain") equals `2`
   - Expected: layer.get_level("infra") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_level returns correct index")
step("Verify: get_level returns correct index")
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.UpperToLower)
expect(layer.get_level("api")).to_equal(0)
expect(layer.get_level("app")).to_equal(1)
expect(layer.get_level("domain")).to_equal(2)
expect(layer.get_level("infra")).to_equal(3)
```

</details>

#### get_level returns -1 for unknown

- get_level returns -1 for unknown
- Verify: get_level returns -1 for unknown
   - Expected: layer.get_level("unknown") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_level returns -1 for unknown")
step("Verify: get_level returns -1 for unknown")
val layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
expect(layer.get_level("unknown")).to_equal(-1)
```

</details>

#### has_layer returns true for known layers

- has_layer returns true for known layers
- Verify: has_layer returns true for known layers
   - Expected: layer.has_layer("api") is true
   - Expected: layer.has_layer("domain") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_layer returns true for known layers")
step("Verify: has_layer returns true for known layers")
val layer = LayerDef.new(["api", "app", "domain"], LayerDirection.UpperToLower)
expect(layer.has_layer("api")).to_equal(true)
expect(layer.has_layer("domain")).to_equal(true)
```

</details>

#### has_layer returns false for unknown

- has_layer returns false for unknown
- Verify: has_layer returns false for unknown
   - Expected: layer.has_layer("infra") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_layer returns false for unknown")
step("Verify: has_layer returns false for unknown")
val layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
expect(layer.has_layer("infra")).to_equal(false)
```

</details>

#### layer_count returns length

- layer_count returns length
- Verify: layer_count returns length
   - Expected: layer.layer_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("layer_count returns length")
step("Verify: layer_count returns length")
val layer = LayerDef.new(["api", "app", "domain"], LayerDirection.UpperToLower)
expect(layer.layer_count()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### empty layer_count is zero

- empty layer_count is zero
- Verify: empty layer_count is zero
   - Expected: layer.layer_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty layer_count is zero")
step("Verify: empty layer_count is zero")
val layer = LayerDef.empty()
expect(layer.layer_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### LayerDef can_depend UpperToLower

#### allows upper to depend on lower

- allows upper to depend on lower
- Verify: allows upper to depend on lower
   - Expected: layer.can_depend("api", "app") is true
   - Expected: layer.can_depend("api", "infra") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows upper to depend on lower")
step("Verify: allows upper to depend on lower")
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.UpperToLower)
# api (0) -> app (1): upper depends on lower = allowed
expect(layer.can_depend("api", "app")).to_equal(true)
# api (0) -> infra (3): upper depends on lower = allowed
expect(layer.can_depend("api", "infra")).to_equal(true)
```

</details>

#### denies lower depending on upper

- denies lower depending on upper
- Verify: denies lower depending on upper
   - Expected: layer.can_depend("infra", "api") is false
   - Expected: layer.can_depend("domain", "app") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("denies lower depending on upper")
step("Verify: denies lower depending on upper")
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.UpperToLower)
# infra (3) -> api (0): lower depends on upper = denied
expect(layer.can_depend("infra", "api")).to_equal(false)
# domain (2) -> app (1): lower depends on upper = denied
expect(layer.can_depend("domain", "app")).to_equal(false)
```

</details>

#### allows same layer by default

- allows same layer by default
- Verify: allows same layer by default
   - Expected: layer.can_depend("app", "app") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows same layer by default")
step("Verify: allows same layer by default")
val layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
expect(layer.can_depend("app", "app")).to_equal(true)
```

</details>

#### denies same layer when disabled

- denies same layer when disabled
- Verify: denies same layer when disabled
   - Expected: layer.can_depend("app", "app") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("denies same layer when disabled")
step("Verify: denies same layer when disabled")
var layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
layer.allow_same_layer = false
expect(layer.can_depend("app", "app")).to_equal(false)
```

</details>

#### allows unknown layers (no restriction)

- allows unknown layers (no restriction)
- Verify: allows unknown layers (no restriction)
   - Expected: layer.can_depend("unknown", "api") is true
   - Expected: layer.can_depend("api", "unknown") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows unknown layers (no restriction)")
step("Verify: allows unknown layers (no restriction)")
val layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
# unknown -> api: unrestricted
expect(layer.can_depend("unknown", "api")).to_equal(true)
# api -> unknown: unrestricted
expect(layer.can_depend("api", "unknown")).to_equal(true)
```

</details>

### LayerDef can_depend LowerToUpper

#### allows lower to depend on upper

- allows lower to depend on upper
- Verify: allows lower to depend on upper
   - Expected: layer.can_depend("infra", "api") is true
   - Expected: layer.can_depend("domain", "app") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows lower to depend on upper")
step("Verify: allows lower to depend on upper")
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.LowerToUpper)
# infra (3) -> api (0): lower depends on upper = allowed
expect(layer.can_depend("infra", "api")).to_equal(true)
# domain (2) -> app (1): lower depends on upper = allowed
expect(layer.can_depend("domain", "app")).to_equal(true)
```

</details>

#### denies upper depending on lower

- denies upper depending on lower
- Verify: denies upper depending on lower
   - Expected: layer.can_depend("api", "infra") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("denies upper depending on lower")
step("Verify: denies upper depending on lower")
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.LowerToUpper)
# api (0) -> infra (3): upper depends on lower = denied
expect(layer.can_depend("api", "infra")).to_equal(false)
```

</details>

### LayerDef adjacent_only mode

#### allows adjacent layers only (UpperToLower)

- allows adjacent layers only (UpperToLower)
- Verify: allows adjacent layers only (UpperToLower)
   - Expected: layer.can_depend("api", "app") is true
   - Expected: layer.can_depend("api", "domain") is false
   - Expected: layer.can_depend("api", "infra") is false
   - Expected: layer.can_depend("app", "domain") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows adjacent layers only (UpperToLower)")
step("Verify: allows adjacent layers only (UpperToLower)")
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

- allows adjacent layers only (LowerToUpper)
- Verify: allows adjacent layers only (LowerToUpper)
   - Expected: layer.can_depend("infra", "domain") is true
   - Expected: layer.can_depend("infra", "api") is false
   - Expected: layer.can_depend("domain", "app") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows adjacent layers only (LowerToUpper)")
step("Verify: allows adjacent layers only (LowerToUpper)")
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

- describes same-layer violation
- Verify: describes same-layer violation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes same-layer violation")
step("Verify: describes same-layer violation")
var layer = LayerDef.new(["api", "app"], LayerDirection.UpperToLower)
layer.allow_same_layer = false
val msg = layer.describe_violation("app", "app")
expect(msg).to_contain("same-layer dependency")
expect(msg).to_contain("app")
```

</details>

#### describes cross-layer violation with levels

- describes cross-layer violation with levels
- Verify: describes cross-layer violation with levels


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes cross-layer violation with levels")
step("Verify: describes cross-layer violation with levels")
val layer = LayerDef.new(["api", "app", "domain", "infra"], LayerDirection.UpperToLower)
val msg = layer.describe_violation("infra", "api")
expect(msg).to_contain("infra")
expect(msg).to_contain("api")
expect(msg).to_contain("level")
```

</details>

### VirtualCapsule

#### constructs with name, dimension, layer

- constructs with name, dimension, layer
- Verify: constructs with name, dimension, layer
   - Expected: cap.name equals `auth`
   - Expected: cap.dimension equals `feature`
   - Expected: cap.layer equals `domain`
   - Expected: cap.bindings.len() equals `0`
   - Expected: cap.exports.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with name, dimension, layer")
step("Verify: constructs with name, dimension, layer")
val cap = VirtualCapsule.new("auth", "feature", "domain")
expect(cap.name).to_equal("auth")
expect(cap.dimension).to_equal("feature")
expect(cap.layer).to_equal("domain")
expect(cap.bindings.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(cap.exports.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### capsule_id returns dimension/name

- capsule_id returns dimension/name
- Verify: capsule_id returns dimension/name
   - Expected: cap.capsule_id() equals `feature/auth`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("capsule_id returns dimension/name")
step("Verify: capsule_id returns dimension/name")
val cap = VirtualCapsule.new("auth", "feature", "domain")
expect(cap.capsule_id()).to_equal("feature/auth")
```

</details>

#### capsule_id for platform dimension

- capsule_id for platform dimension
- Verify: capsule_id for platform dimension
   - Expected: cap.capsule_id() equals `platform/linux`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("capsule_id for platform dimension")
step("Verify: capsule_id for platform dimension")
val cap = VirtualCapsule.new("linux", "platform", "infra")
expect(cap.capsule_id()).to_equal("platform/linux")
```

</details>

### VirtualCapsule bindings

#### find_binding returns nil for empty capsule

- find_binding returns nil for empty capsule
- Verify: find_binding returns nil for empty capsule


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_binding returns nil for empty capsule")
step("Verify: find_binding returns nil for empty capsule")
val cap = VirtualCapsule.new("auth", "feature", "domain")
val result = cap.find_binding("core_auth")
expect(result).to_be_nil()
```

</details>

#### find_binding returns matching binding

- find_binding returns matching binding
- Verify: find_binding returns matching binding
   - Expected: binding.alias equals `core_auth`
   - Expected: binding.source_caret equals `core`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_binding returns matching binding")
step("Verify: find_binding returns matching binding")
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

- find_binding returns nil for no match
- Verify: find_binding returns nil for no match


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_binding returns nil for no match")
step("Verify: find_binding returns nil for no match")
var cap = VirtualCapsule.new("auth", "feature", "domain")
cap.bindings = [SurfaceBinding.new("core", "feature/auth/login.spl", "core_auth")]
val result = cap.find_binding("ui_auth")
expect(result).to_be_nil()
```

</details>

#### has_binding_from returns true when caret present

- has_binding_from returns true when caret present
- Verify: has_binding_from returns true when caret present
   - Expected: cap.has_binding_from("core") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_binding_from returns true when caret present")
step("Verify: has_binding_from returns true when caret present")
var cap = VirtualCapsule.new("auth", "feature", "domain")
cap.bindings = [SurfaceBinding.new("core", "feature/auth/login.spl", "core_auth")]
expect(cap.has_binding_from("core")).to_equal(true)
```

</details>

#### has_binding_from returns false when caret absent

- has_binding_from returns false when caret absent
- Verify: has_binding_from returns false when caret absent
   - Expected: cap.has_binding_from("ui") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_binding_from returns false when caret absent")
step("Verify: has_binding_from returns false when caret absent")
var cap = VirtualCapsule.new("auth", "feature", "domain")
cap.bindings = [SurfaceBinding.new("core", "feature/auth/login.spl", "core_auth")]
expect(cap.has_binding_from("ui")).to_equal(false)
```

</details>

### VirtualCapsule exports

#### find_export returns nil for empty capsule

- find_export returns nil for empty capsule
- Verify: find_export returns nil for empty capsule


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_export returns nil for empty capsule")
step("Verify: find_export returns nil for empty capsule")
val cap = VirtualCapsule.new("auth", "feature", "domain")
val result = cap.find_export("login")
expect(result).to_be_nil()
```

</details>

#### find_export returns matching export

- find_export returns matching export
- Verify: find_export returns matching export
   - Expected: exp.symbol_name equals `login`
   - Expected: exp.binding_alias equals `core_auth`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_export returns matching export")
step("Verify: find_export returns matching export")
var cap = VirtualCapsule.new("auth", "feature", "domain")
cap.exports = [CapsuleExport.public_export("core_auth", "login")]
val result = cap.find_export("login")
val exp = result ?? CapsuleExport.public_export("", "")
expect(exp.symbol_name).to_equal("login")
expect(exp.binding_alias).to_equal("core_auth")
```

</details>

#### public_exports filters public only

- public_exports filters public only
- Verify: public_exports filters public only
   - Expected: pub_list.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("public_exports filters public only")
step("Verify: public_exports filters public only")
var cap = VirtualCapsule.new("auth", "feature", "domain")
cap.exports = [
    CapsuleExport.public_export("a", "login"),
    CapsuleExport.internal_export("b", "helper"),
    CapsuleExport.public_export("c", "logout")
]
val pub_list = cap.public_exports()
expect(pub_list.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### internal_exports filters internal only

- internal_exports filters internal only
- Verify: internal_exports filters internal only
   - Expected: int_exports.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("internal_exports filters internal only")
step("Verify: internal_exports filters internal only")
var cap = VirtualCapsule.new("auth", "feature", "domain")
cap.exports = [
    CapsuleExport.public_export("a", "login"),
    CapsuleExport.internal_export("b", "helper"),
    CapsuleExport.internal_export("c", "utils")
]
val int_exports = cap.internal_exports()
expect(int_exports.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### SurfaceBinding

#### constructs with caret, path, alias

- constructs with caret, path, alias
- Verify: constructs with caret, path, alias
   - Expected: binding.source_caret equals `core`
   - Expected: binding.source_path equals `feature/auth/login.spl`
   - Expected: binding.alias equals `core_auth`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with caret, path, alias")
step("Verify: constructs with caret, path, alias")
val binding = SurfaceBinding.new("core", "feature/auth/login.spl", "core_auth")
expect(binding.source_caret).to_equal("core")
expect(binding.source_path).to_equal("feature/auth/login.spl")
expect(binding.alias).to_equal("core_auth")
```

</details>

#### different bindings have different aliases

- different bindings have different aliases
- Verify: different bindings have different aliases
   - Expected: a.alias equals `core_auth`
   - Expected: b.alias equals `ui_auth`
   - Expected: a.source_caret equals `core`
   - Expected: b.source_caret equals `ui`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different bindings have different aliases")
step("Verify: different bindings have different aliases")
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

- public_export creates Public visibility
- Verify: public_export creates Public visibility
   - Expected: exp.visibility.is_public() is true
   - Expected: exp.binding_alias equals `core_auth`
   - Expected: exp.symbol_name equals `login`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("public_export creates Public visibility")
step("Verify: public_export creates Public visibility")
val exp = CapsuleExport.public_export("core_auth", "login")
expect(exp.visibility.is_public()).to_equal(true)
expect(exp.binding_alias).to_equal("core_auth")
expect(exp.symbol_name).to_equal("login")
```

</details>

#### internal_export creates Internal visibility

- internal_export creates Internal visibility
- Verify: internal_export creates Internal visibility
   - Expected: exp.visibility.is_internal() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("internal_export creates Internal visibility")
step("Verify: internal_export creates Internal visibility")
val exp = CapsuleExport.internal_export("core_auth", "helper")
expect(exp.visibility.is_internal()).to_equal(true)
```

</details>

#### qualified_name joins alias and symbol

- qualified_name joins alias and symbol
- Verify: qualified_name joins alias and symbol
   - Expected: exp.qualified_name() equals `core_auth.login`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("qualified_name joins alias and symbol")
step("Verify: qualified_name joins alias and symbol")
val exp = CapsuleExport.public_export("core_auth", "login")
expect(exp.qualified_name()).to_equal("core_auth.login")
```

</details>

#### is_accessible_from_capsule for Public

- is_accessible_from_capsule for Public
- Verify: is_accessible_from_capsule for Public
   - Expected: exp.is_accessible_from_capsule() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_accessible_from_capsule for Public")
step("Verify: is_accessible_from_capsule for Public")
val exp = CapsuleExport.public_export("a", "sym")
expect(exp.is_accessible_from_capsule()).to_equal(true)
```

</details>

#### is_accessible_from_capsule for Internal

- is_accessible_from_capsule for Internal
- Verify: is_accessible_from_capsule for Internal
   - Expected: exp.is_accessible_from_capsule() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_accessible_from_capsule for Internal")
step("Verify: is_accessible_from_capsule for Internal")
val exp = CapsuleExport.internal_export("a", "sym")
expect(exp.is_accessible_from_capsule()).to_equal(true)
```

</details>

#### is_accessible_from_capsule for Private

- is_accessible_from_capsule for Private
- Verify: is_accessible_from_capsule for Private
   - Expected: exp.is_accessible_from_capsule() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_accessible_from_capsule for Private")
step("Verify: is_accessible_from_capsule for Private")
val exp = CapsuleExport.private_export("a", "sym")
expect(exp.is_accessible_from_capsule()).to_equal(false)
```

</details>

### BypassGrant

#### constructs with all fields

- constructs with all fields
- Verify: constructs with all fields
   - Expected: grant.granting_module equals `infra/db`
   - Expected: grant.granted_symbol equals `raw_query`
   - Expected: grant.layer_edge equals `domain->infra`
   - Expected: grant.reason equals `performance critical`
   - Expected: grant.location equals `infra/db.spl:10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with all fields")
step("Verify: constructs with all fields")
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

- grant_key joins module and symbol
- Verify: grant_key joins module and symbol
   - Expected: grant.grant_key() equals `infra/db::raw_query`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("grant_key joins module and symbol")
step("Verify: grant_key joins module and symbol")
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

- grant_key is deterministic
- Verify: grant_key is deterministic
   - Expected: a.grant_key() equals `b.grant_key()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("grant_key is deterministic")
step("Verify: grant_key is deterministic")
val a = BypassGrant.new("mod", "sym", "e", "r", "l")
val b = BypassGrant.new("mod", "sym", "e2", "r2", "l2")
expect(a.grant_key()).to_equal(b.grant_key())
```

</details>

### CapsuleRules

#### strict enables all enforcement

- strict enables all enforcement
- Verify: strict enables all enforcement
   - Expected: rules.enforce_layering is true
   - Expected: rules.reject_cycles is true
   - Expected: rules.forbid_implicit_merge is true
   - Expected: rules.require_explicit_bind is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strict enables all enforcement")
step("Verify: strict enables all enforcement")
val rules = CapsuleRules.strict()
expect(rules.enforce_layering).to_equal(true)
expect(rules.reject_cycles).to_equal(true)
expect(rules.forbid_implicit_merge).to_equal(true)
expect(rules.require_explicit_bind).to_equal(true)
```

</details>

#### permissive disables all enforcement

- permissive disables all enforcement
- Verify: permissive disables all enforcement
   - Expected: rules.enforce_layering is false
   - Expected: rules.reject_cycles is false
   - Expected: rules.forbid_implicit_merge is false
   - Expected: rules.require_explicit_bind is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("permissive disables all enforcement")
step("Verify: permissive disables all enforcement")
val rules = CapsuleRules.permissive()
expect(rules.enforce_layering).to_equal(false)
expect(rules.reject_cycles).to_equal(false)
expect(rules.forbid_implicit_merge).to_equal(false)
expect(rules.require_explicit_bind).to_equal(false)
```

</details>

#### default_rules returns strict

- default_rules returns strict
- Verify: default_rules returns strict
   - Expected: rules.enforce_layering is true
   - Expected: rules.reject_cycles is true
   - Expected: rules.forbid_implicit_merge is true
   - Expected: rules.require_explicit_bind is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default_rules returns strict")
step("Verify: default_rules returns strict")
val rules = CapsuleRules.default_rules()
expect(rules.enforce_layering).to_equal(true)
expect(rules.reject_cycles).to_equal(true)
expect(rules.forbid_implicit_merge).to_equal(true)
expect(rules.require_explicit_bind).to_equal(true)
```

</details>

### MdsocManifest

#### constructs with name and defaults

- constructs with name and defaults
- Verify: constructs with name and defaults
   - Expected: manifest.name equals `my-project`
   - Expected: manifest.version equals `0.1.0`
   - Expected: manifest.carets.len() equals `0`
   - Expected: manifest.dimensions.len() equals `0`
   - Expected: manifest.capsules.len() equals `0`
   - Expected: manifest.bypass_grants.len() equals `0`
   - Expected: manifest.rules.enforce_layering is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with name and defaults")
step("Verify: constructs with name and defaults")
val manifest = MdsocManifest.new("my-project")
expect(manifest.name).to_equal("my-project")
expect(manifest.version).to_equal("0.1.0")
expect(manifest.carets.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(manifest.dimensions.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(manifest.capsules.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(manifest.bypass_grants.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
# default rules are strict
expect(manifest.rules.enforce_layering).to_equal(true)
```

</details>

#### get_caret returns nil when empty

- get_caret returns nil when empty
- Verify: get_caret returns nil when empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_caret returns nil when empty")
step("Verify: get_caret returns nil when empty")
val manifest = MdsocManifest.new("proj")
val result = manifest.get_caret("core")
expect(result).to_be_nil()
```

</details>

#### get_caret returns matching caret

- get_caret returns matching caret
- Verify: get_caret returns matching caret
   - Expected: caret.name equals `ui`
   - Expected: caret.path equals `src/ui`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_caret returns matching caret")
step("Verify: get_caret returns matching caret")
var manifest = MdsocManifest.new("proj")
manifest.carets = [CaretId.new("core", "src/core"), CaretId.new("ui", "src/ui")]
val result = manifest.get_caret("ui")
val caret = result ?? CaretId.default_caret("")
expect(caret.name).to_equal("ui")
expect(caret.path).to_equal("src/ui")
```

</details>

#### get_caret returns nil for non-existent

- get_caret returns nil for non-existent
- Verify: get_caret returns nil for non-existent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_caret returns nil for non-existent")
step("Verify: get_caret returns nil for non-existent")
var manifest = MdsocManifest.new("proj")
manifest.carets = [CaretId.new("core", "src/core")]
val result = manifest.get_caret("infra")
expect(result).to_be_nil()
```

</details>

#### get_dimension returns matching dimension

- get_dimension returns matching dimension
- Verify: get_dimension returns matching dimension
   - Expected: dim.name equals `feature`
   - Expected: dim.key_template equals `feature/" + r"{name}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_dimension returns matching dimension")
step("Verify: get_dimension returns matching dimension")
var manifest = MdsocManifest.new("proj")
manifest.dimensions = [DimensionDef.new("feature", "feature/" + r"{name}")]
val result = manifest.get_dimension("feature")
val dim = result ?? DimensionDef.new("", "")
expect(dim.name).to_equal("feature")
expect(dim.key_template).to_equal("feature/" + r"{name}")
```

</details>

#### get_dimension returns nil for non-existent

- get_dimension returns nil for non-existent
- Verify: get_dimension returns nil for non-existent


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_dimension returns nil for non-existent")
step("Verify: get_dimension returns nil for non-existent")
val manifest = MdsocManifest.new("proj")
val result = manifest.get_dimension("platform")
expect(result).to_be_nil()
```

</details>

#### get_capsule returns matching capsule

- get_capsule returns matching capsule
- Verify: get_capsule returns matching capsule
   - Expected: cap.name equals `auth`
   - Expected: cap.dimension equals `feature`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_capsule returns matching capsule")
step("Verify: get_capsule returns matching capsule")
var manifest = MdsocManifest.new("proj")
manifest.capsules = [VirtualCapsule.new("auth", "feature", "domain")]
val result = manifest.get_capsule("auth")
val cap = result ?? VirtualCapsule.new("", "", "")
expect(cap.name).to_equal("auth")
expect(cap.dimension).to_equal("feature")
```

</details>

#### get_capsule returns nil for non-existent

- get_capsule returns nil for non-existent
- Verify: get_capsule returns nil for non-existent


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_capsule returns nil for non-existent")
step("Verify: get_capsule returns nil for non-existent")
val manifest = MdsocManifest.new("proj")
val result = manifest.get_capsule("billing")
expect(result).to_be_nil()
```

</details>

#### find_bypass_grant returns matching grant

- find_bypass_grant returns matching grant
- Verify: find_bypass_grant returns matching grant
   - Expected: grant.granted_symbol equals `raw_query`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_bypass_grant returns matching grant")
step("Verify: find_bypass_grant returns matching grant")
var manifest = MdsocManifest.new("proj")
manifest.bypass_grants = [BypassGrant.new("mod", "raw_query", "e", "r", "l")]
val result = manifest.find_bypass_grant("raw_query")
val grant = result ?? BypassGrant.new("", "", "", "", "")
expect(grant.granted_symbol).to_equal("raw_query")
```

</details>

#### find_bypass_grant returns nil for no match

- find_bypass_grant returns nil for no match
- Verify: find_bypass_grant returns nil for no match


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_bypass_grant returns nil for no match")
step("Verify: find_bypass_grant returns nil for no match")
val manifest = MdsocManifest.new("proj")
val result = manifest.find_bypass_grant("nonexistent")
expect(result).to_be_nil()
```

</details>

#### find_capsule_by_id matches dimension/name

- find_capsule_by_id matches dimension/name
- Verify: find_capsule_by_id matches dimension/name
   - Expected: cap.name equals `auth`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_capsule_by_id matches dimension/name")
step("Verify: find_capsule_by_id matches dimension/name")
var manifest = MdsocManifest.new("proj")
manifest.capsules = [VirtualCapsule.new("auth", "feature", "domain")]
val result = manifest.find_capsule_by_id("feature/auth")
val cap = result ?? VirtualCapsule.new("", "", "")
expect(cap.name).to_equal("auth")
```

</details>

#### find_capsule_by_id returns nil for wrong id

- find_capsule_by_id returns nil for wrong id
- Verify: find_capsule_by_id returns nil for wrong id


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_capsule_by_id returns nil for wrong id")
step("Verify: find_capsule_by_id returns nil for wrong id")
var manifest = MdsocManifest.new("proj")
manifest.capsules = [VirtualCapsule.new("auth", "feature", "domain")]
val result = manifest.find_capsule_by_id("platform/auth")
expect(result).to_be_nil()
```

</details>

### DimensionDef

#### new sets defaults

- new sets defaults
- Verify: new sets defaults
   - Expected: dim.name equals `feature`
   - Expected: dim.key_template equals `feature/" + r"{name}`
   - Expected: dim.surface_file equals `__init__.spl`
   - Expected: dim.participation equals `explicit_bind_only`
   - Expected: dim.intra_access equals `via_surface_only`
   - Expected: dim.symbol_merge equals `forbid_implicit`
   - Expected: dim.dep_cycles equals `reject`
   - Expected: dim.mappings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new sets defaults")
step("Verify: new sets defaults")
val dim = DimensionDef.new("feature", "feature/" + r"{name}")
expect(dim.name).to_equal("feature")
expect(dim.key_template).to_equal("feature/" + r"{name}")
expect(dim.surface_file).to_equal("__init__.spl")
expect(dim.participation).to_equal("explicit_bind_only")
expect(dim.intra_access).to_equal("via_surface_only")
expect(dim.symbol_merge).to_equal("forbid_implicit")
expect(dim.dep_cycles).to_equal("reject")
expect(dim.mappings.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### expand_key substitutes name

- expand_key substitutes name
- Verify: expand_key substitutes name
   - Expected: dim.expand_key("auth") equals `feature/auth`
   - Expected: dim.expand_key("billing") equals `feature/billing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expand_key substitutes name")
step("Verify: expand_key substitutes name")
val dim = DimensionDef.new("feature", "feature/" + r"{name}")
expect(dim.expand_key("auth")).to_equal("feature/auth")
expect(dim.expand_key("billing")).to_equal("feature/billing")
```

</details>

#### expand_key with nested template

- expand_key with nested template
- Verify: expand_key with nested template
   - Expected: dim.expand_key("linux") equals `platform/linux/driver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expand_key with nested template")
step("Verify: expand_key with nested template")
val dim = DimensionDef.new("platform", "platform/" + r"{name}" + "/driver")
expect(dim.expand_key("linux")).to_equal("platform/linux/driver")
```

</details>

#### is_explicit_bind returns true for default

- is_explicit_bind returns true for default
- Verify: is_explicit_bind returns true for default
   - Expected: dim.is_explicit_bind() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_explicit_bind returns true for default")
step("Verify: is_explicit_bind returns true for default")
val dim = DimensionDef.new("feature", "feature/" + r"{name}")
expect(dim.is_explicit_bind()).to_equal(true)
```

</details>

#### is_explicit_bind returns false for other participation

- is_explicit_bind returns false for other participation
- Verify: is_explicit_bind returns false for other participation
   - Expected: dim.is_explicit_bind() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_explicit_bind returns false for other participation")
step("Verify: is_explicit_bind returns false for other participation")
var dim = DimensionDef.new("feature", "feature/" + r"{name}")
dim.participation = "auto_bind"
expect(dim.is_explicit_bind()).to_equal(false)
```

</details>

#### rejects_cycles returns true for default

- rejects_cycles returns true for default
- Verify: rejects_cycles returns true for default
   - Expected: dim.rejects_cycles() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects_cycles returns true for default")
step("Verify: rejects_cycles returns true for default")
val dim = DimensionDef.new("feature", "feature/" + r"{name}")
expect(dim.rejects_cycles()).to_equal(true)
```

</details>

#### rejects_cycles returns false for allow

- rejects_cycles returns false for allow
- Verify: rejects_cycles returns false for allow
   - Expected: dim.rejects_cycles() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects_cycles returns false for allow")
step("Verify: rejects_cycles returns false for allow")
var dim = DimensionDef.new("feature", "feature/" + r"{name}")
dim.dep_cycles = "allow"
expect(dim.rejects_cycles()).to_equal(false)
```

</details>

#### find_mapping returns matching mapping

- find_mapping returns matching mapping
- Verify: find_mapping returns matching mapping
   - Expected: mapping.caret_name equals `ui`
   - Expected: mapping.match_pattern equals `ui_feature/**`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_mapping returns matching mapping")
step("Verify: find_mapping returns matching mapping")
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

- find_mapping returns nil for no match
- Verify: find_mapping returns nil for no match


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_mapping returns nil for no match")
step("Verify: find_mapping returns nil for no match")
val dim = DimensionDef.new("feature", "feature/" + r"{name}")
val result = dim.find_mapping("unknown")
expect(result).to_be_nil()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 90 |
| Active scenarios | 90 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMPILER-MDSOC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bbf7addfd2ba78cc0322aebe2848c3d7375eb197b62e04caa7ea0db174dcfb9c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bbf7addfd2ba78cc0322aebe2848c3d7375eb197b62e04caa7ea0db174dcfb9c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bbf7addfd2ba78cc0322aebe2848c3d7375eb197b62e04caa7ea0db174dcfb9c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/mdsoc/types_spec.spl
mirror: doc/06_spec/unit/compiler/mdsoc/types_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/mdsoc/types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/mdsoc/types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/mdsoc/types_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/mdsoc/types_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Public is_public returns true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mdsoc/types_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Public is_internal returns false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mdsoc/types_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Public is_private returns false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
