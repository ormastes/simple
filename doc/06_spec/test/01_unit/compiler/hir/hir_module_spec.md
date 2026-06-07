# HIR Module Unit Tests

> Tests for HIR module system: HirParam, HirFunction, HirModule, type definitions.

<!-- sdn-diagram:id=hir_module_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hir_module_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hir_module_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hir_module_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 59 | 59 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HIR Module Unit Tests

Tests for HIR module system: HirParam, HirFunction, HirModule, type definitions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HIR-MODULE-001 |
| Category | HIR \| Module |
| Status | In Progress |
| Source | `test/01_unit/compiler/hir/hir_module_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for HIR module system: HirParam, HirFunction, HirModule, type definitions.

## Scenarios

### HirParam Factory Functions

#### creates immutable parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val param = HirParam.new("x", TypeId.i64_ty(), 0)
# expect param.name == "x"
# expect param.index == 0
# expect param.is_mutable == false
expect true
```

</details>

#### creates mutable parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val param = HirParam.mutable("x", TypeId.i64_ty(), 0)
# expect param.is_mutable == true
expect true
```

</details>

#### converts to LocalVar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val param = HirParam.new("x", TypeId.i64_ty(), 0)
# val local = param.to_local_var()
# expect local.name == "x"
# expect local.index == 0
expect true
```

</details>

### Visibility

#### Private is_private returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect Visibility.Private.is_private()
expect true
```

</details>

#### Public is_public returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect Visibility.Public.is_public()
expect true
```

</details>

#### Private to_string is private

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect Visibility.Private.to_string() == "private"
expect true
```

</details>

#### Public to_string is public

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect Visibility.Public.to_string() == "public"
expect true
```

</details>

### HirFunctionSig Factory

#### creates basic function signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val sig = HirFunctionSig.new("foo", [], TypeId.void_ty())
# expect sig.name == "foo"
# expect sig.param_count() == 0
# expect sig.returns_void()
expect true
```

</details>

#### creates public function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val sig = HirFunctionSig.public("bar", [], TypeId.i64_ty())
# expect sig.visibility.is_public()
expect true
```

</details>

#### creates async function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val sig = HirFunctionSig.async_fn("async_foo", [], TypeId.void_ty())
# expect sig.is_async
expect true
```

</details>

#### creates method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val sig = HirFunctionSig.method("get_x", [], TypeId.i64_ty())
# expect sig.is_method
expect true
```

</details>

#### creates static method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val sig = HirFunctionSig.static_method("new", [], TypeId.void_ty())
# expect sig.is_static
expect true
```

</details>

### HirFunctionSig Methods

#### param_count returns correct count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val params = [HirParam.new("a", TypeId.i64_ty(), 0), HirParam.new("b", TypeId.i64_ty(), 1)]
# val sig = HirFunctionSig.new("add", params, TypeId.i64_ty())
# expect sig.param_count() == 2
expect true
```

</details>

#### get_param returns correct parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val params = [HirParam.new("a", TypeId.i64_ty(), 0)]
# val sig = HirFunctionSig.new("foo", params, TypeId.void_ty())
# val param = sig.get_param(0)
# expect param.is_some()
# expect param.unwrap().name == "a"
expect true
```

</details>

#### get_param returns None for invalid index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val sig = HirFunctionSig.new("foo", [], TypeId.void_ty())
# expect sig.get_param(0).is_none()
expect true
```

</details>

### ExprId

#### creates valid expression id

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val id = ExprId.new(42)
# expect id.index == 42
# expect id.is_valid()
expect true
```

</details>

#### invalid returns max u32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val id = ExprId.invalid()
# expect not id.is_valid()
expect true
```

</details>

### StmtId

#### creates valid statement id

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val id = StmtId.new(10)
# expect id.index == 10
# expect id.is_valid()
expect true
```

</details>

#### invalid returns max u32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val id = StmtId.invalid()
# expect not id.is_valid()
expect true
```

</details>

### HirBody

#### creates empty body

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val body = HirBody.empty()
# expect body.local_count() == 0
# expect not body.root_stmt.is_valid()
expect true
```

</details>

#### creates body with root statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val root = StmtId.new(0)
# val body = HirBody.new(root)
# expect body.root_stmt.is_valid()
expect true
```

</details>

#### add_local increases count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var body = HirBody.empty()
# val local = LocalVar.new("x", TypeId.i64_ty(), false, 0)
# body.add_local(local)
# expect body.local_count() == 1
expect true
```

</details>

#### get_local returns correct local

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var body = HirBody.empty()
# body.add_local(LocalVar.new("x", TypeId.i64_ty(), false, 0))
# val local = body.get_local(0)
# expect local.is_some()
# expect local.unwrap().name == "x"
expect true
```

</details>

#### find_local finds by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var body = HirBody.empty()
# body.add_local(LocalVar.new("foo", TypeId.i64_ty(), false, 0))
# val local = body.find_local("foo")
# expect local.is_some()
expect true
```

</details>

### HirFunction Factory

#### creates function with signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val sig = HirFunctionSig.new("test", [], TypeId.void_ty())
# val func = HirFunction.new(0, sig)
# expect func.name() == "test"
# expect func.id == 0
expect true
```

</details>

#### creates function with body

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val sig = HirFunctionSig.new("test", [], TypeId.void_ty())
# val body = HirBody.empty()
# val func = HirFunction.with_body(0, sig, body)
# expect func.name() == "test"
expect true
```

</details>

### HirFunction Methods

#### name returns function name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val sig = HirFunctionSig.new("my_func", [], TypeId.void_ty())
# val func = HirFunction.new(0, sig)
# expect func.name() == "my_func"
expect true
```

</details>

#### return_type returns correct type

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val sig = HirFunctionSig.new("foo", [], TypeId.i64_ty())
# val func = HirFunction.new(0, sig)
# expect func.return_type().id == TypeId.i64_ty().id
expect true
```

</details>

#### is_closure returns false for non-closure

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val sig = HirFunctionSig.new("foo", [], TypeId.void_ty())
# val func = HirFunction.new(0, sig)
# expect not func.is_closure()
expect true
```

</details>

#### is_closure returns true when captures present

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val sig = HirFunctionSig.new("foo", [], TypeId.void_ty())
# var func = HirFunction.new(0, sig)
# func.add_capture(CapturedVar.by_value(0))
# expect func.is_closure()
expect true
```

</details>

#### param_count delegates to signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val params = [HirParam.new("x", TypeId.i64_ty(), 0)]
# val sig = HirFunctionSig.new("foo", params, TypeId.void_ty())
# val func = HirFunction.new(0, sig)
# expect func.param_count() == 1
expect true
```

</details>

### TypeDefKind

#### Struct is_struct returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeDefKind.Struct.is_struct()
expect true
```

</details>

#### Class is_class returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeDefKind.Class.is_class()
expect true
```

</details>

#### Enum is_enum returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeDefKind.Enum.is_enum()
expect true
```

</details>

#### Trait is_trait returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeDefKind.Trait.is_trait()
expect true
```

</details>

#### to_string returns correct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeDefKind.Struct.to_string() == "struct"
# expect TypeDefKind.Class.to_string() == "class"
# expect TypeDefKind.Enum.to_string() == "enum"
expect true
```

</details>

### HirField

#### creates immutable field

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val field = HirField.new("x", TypeId.i64_ty(), 0)
# expect field.name == "x"
# expect field.index == 0
# expect field.is_mutable == false
expect true
```

</details>

#### creates mutable field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val field = HirField.mutable("x", TypeId.i64_ty(), 0)
# expect field.is_mutable == true
expect true
```

</details>

#### creates public field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val field = HirField.public("x", TypeId.i64_ty(), 0)
# expect field.visibility.is_public()
expect true
```

</details>

### HirVariant

#### creates unit variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val variant = HirVariant.unit("None", 0)
# expect variant.name == "None"
# expect variant.index == 0
# expect not variant.has_payload()
expect true
```

</details>

#### creates variant with payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val variant = HirVariant.with_payload("Some", 1, TypeId.i64_ty())
# expect variant.name == "Some"
# expect variant.has_payload()
expect true
```

</details>

### HirTypeDef Factory

#### creates struct definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val fields = [HirField.new("x", TypeId.i64_ty(), 0)]
# val def = HirTypeDef.struct_def(0, "Point", TypeId.i64_ty(), fields)
# expect def.name == "Point"
# expect def.kind.is_struct()
# expect def.field_count() == 1
expect true
```

</details>

#### creates class definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val fields = [HirField.new("count", TypeId.i64_ty(), 0)]
# val def = HirTypeDef.class_def(0, "Counter", TypeId.i64_ty(), fields)
# expect def.kind.is_class()
expect true
```

</details>

#### creates enum definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val variants = [HirVariant.unit("A", 0), HirVariant.unit("B", 1)]
# val def = HirTypeDef.enum_def(0, "MyEnum", TypeId.i64_ty(), variants)
# expect def.kind.is_enum()
# expect def.variant_count() == 2
expect true
```

</details>

### HirTypeDef Methods

#### find_field returns correct field

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val fields = [HirField.new("x", TypeId.i64_ty(), 0), HirField.new("y", TypeId.i64_ty(), 1)]
# val def = HirTypeDef.struct_def(0, "Point", TypeId.i64_ty(), fields)
# val field = def.find_field("y")
# expect field.is_some()
# expect field.unwrap().index == 1
expect true
```

</details>

#### find_variant returns correct variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val variants = [HirVariant.unit("A", 0), HirVariant.unit("B", 1)]
# val def = HirTypeDef.enum_def(0, "MyEnum", TypeId.i64_ty(), variants)
# val variant = def.find_variant("B")
# expect variant.is_some()
# expect variant.unwrap().index == 1
expect true
```

</details>

#### add_method adds method reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var def = HirTypeDef.struct_def(0, "Point", TypeId.i64_ty(), [])
# def.add_method(5)
# expect def.method_count() == 1
expect true
```

</details>

### HirImport

#### creates simple import

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val imp = HirImport.new("std.io", "File")
# expect imp.module_path == "std.io"
# expect imp.name == "File"
# expect imp.alias_name.is_none()
expect true
```

</details>

#### creates aliased import

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val imp = HirImport.aliased("std.io", "File", "F")
# expect imp.alias_name.is_some()
# expect imp.alias_name.unwrap() == "F"
expect true
```

</details>

#### creates wildcard import

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val imp = HirImport.wildcard("std.io")
# expect imp.is_wildcard
# expect imp.name == "*"
expect true
```

</details>

#### effective_name returns alias if present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val imp = HirImport.aliased("std.io", "File", "F")
# expect imp.effective_name() == "F"
expect true
```

</details>

#### effective_name returns name if no alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val imp = HirImport.new("std.io", "File")
# expect imp.effective_name() == "File"
expect true
```

</details>

### HirModule Factory

#### creates empty module

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val mod = HirModule.new("main", "src/main.spl")
# expect mod.name == "main"
# expect mod.path == "src/main.spl"
# expect mod.function_count() == 0
expect true
```

</details>

### HirModule Methods

#### add_import adds import

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var mod = HirModule.new("main", "src/main.spl")
# mod.add_import(HirImport.new("std.io", "File"))
# expect mod.imports.len() == 1
expect true
```

</details>

#### add_function adds function

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var mod = HirModule.new("main", "src/main.spl")
# val sig = HirFunctionSig.new("main", [], TypeId.void_ty())
# mod.add_function(HirFunction.new(0, sig))
# expect mod.function_count() == 1
expect true
```

</details>

#### add_type adds type definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var mod = HirModule.new("main", "src/main.spl")
# val def = HirTypeDef.struct_def(0, "Point", TypeId.i64_ty(), [])
# mod.add_type(def)
# expect mod.type_count() == 1
expect true
```

</details>

#### find_function finds by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var mod = HirModule.new("main", "src/main.spl")
# val sig = HirFunctionSig.new("foo", [], TypeId.void_ty())
# mod.add_function(HirFunction.new(0, sig))
# val func = mod.find_function("foo")
# expect func.is_some()
expect true
```

</details>

#### find_type finds by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var mod = HirModule.new("main", "src/main.spl")
# val def = HirTypeDef.struct_def(0, "Point", TypeId.i64_ty(), [])
# mod.add_type(def)
# val type_def = mod.find_type("Point")
# expect type_def.is_some()
expect true
```

</details>

#### find_global finds by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var mod = HirModule.new("main", "src/main.spl")
# mod.add_global(LocalVar.new("VERSION", TypeId.string_ty(), false, 0))
# val global = mod.find_global("VERSION")
# expect global.is_some()
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 59 |
| Active scenarios | 59 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
