# Hir Module Specification

> Tests covering HirParam Factory Functions, Visibility, HirFunctionSig Factory, HirFunctionSig Methods, ExprId, StmtId, HirBody, HirFunction Factory, HirFunction Methods, TypeDefKind, HirField, HirVariant, HirTypeDef Factory, HirTypeDef Methods, HirImport, HirModule Factory, HirModule Methods.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 59 | 59 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Module Specification

## Scenarios

### HirParam Factory Functions

#### creates immutable parameter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates immutable parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates immutable parameter")
# val param = HirParam.new("x", TypeId.i64_ty(), 0)
# expect param.name == "x"
# expect param.index == 0
# expect param.is_mutable == false
expect true
```

</details>

#### creates mutable parameter

- creates mutable parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates mutable parameter")
# val param = HirParam.mutable("x", TypeId.i64_ty(), 0)
# expect param.is_mutable == true
expect true
```

</details>

#### converts to LocalVar

- converts to LocalVar


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to LocalVar")
# val param = HirParam.new("x", TypeId.i64_ty(), 0)
# val local = param.to_local_var()
# expect local.name == "x"
# expect local.index == 0
expect true
```

</details>

### Visibility

#### Private is_private returns true

- Private is_private returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Private is_private returns true")
# expect Visibility.Private.is_private()
expect true
```

</details>

#### Public is_public returns true

- Public is_public returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Public is_public returns true")
# expect Visibility.Public.is_public()
expect true
```

</details>

#### Private to_string is private

- Private to_string is private


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Private to_string is private")
# expect Visibility.Private.to_string() == "private"
expect true
```

</details>

#### Public to_string is public

- Public to_string is public


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Public to_string is public")
# expect Visibility.Public.to_string() == "public"
expect true
```

</details>

### HirFunctionSig Factory

#### creates basic function signature

- creates basic function signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates basic function signature")
# val sig = HirFunctionSig.new("foo", [], TypeId.void_ty())
# expect sig.name == "foo"
# expect sig.param_count() == 0
# expect sig.returns_void()
expect true
```

</details>

#### creates public function

- creates public function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates public function")
# val sig = HirFunctionSig.public("bar", [], TypeId.i64_ty())
# expect sig.visibility.is_public()
expect true
```

</details>

#### creates async function

- creates async function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates async function")
# val sig = HirFunctionSig.async_fn("async_foo", [], TypeId.void_ty())
# expect sig.is_async
expect true
```

</details>

#### creates method

- creates method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates method")
# val sig = HirFunctionSig.method("get_x", [], TypeId.i64_ty())
# expect sig.is_method
expect true
```

</details>

#### creates static method

- creates static method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates static method")
# val sig = HirFunctionSig.static_method("new", [], TypeId.void_ty())
# expect sig.is_static
expect true
```

</details>

### HirFunctionSig Methods

#### param_count returns correct count

- param_count returns correct count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("param_count returns correct count")
# val params = [HirParam.new("a", TypeId.i64_ty(), 0), HirParam.new("b", TypeId.i64_ty(), 1)]
# val sig = HirFunctionSig.new("add", params, TypeId.i64_ty())
# expect sig.param_count() == 2
expect true
```

</details>

#### get_param returns correct parameter

- get_param returns correct parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_param returns correct parameter")
# val params = [HirParam.new("a", TypeId.i64_ty(), 0)]
# val sig = HirFunctionSig.new("foo", params, TypeId.void_ty())
# val param = sig.get_param(0)
# expect param.is_some()
# expect param.unwrap().name == "a"
expect true
```

</details>

#### get_param returns None for invalid index

- get_param returns None for invalid index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_param returns None for invalid index")
# val sig = HirFunctionSig.new("foo", [], TypeId.void_ty())
# expect sig.get_param(0).is_none()
expect true
```

</details>

### ExprId

#### creates valid expression id

- creates valid expression id


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates valid expression id")
# val id = ExprId.new(42)
# expect id.index == 42
# expect id.is_valid()
expect true
```

</details>

#### invalid returns max u32

- invalid returns max u32


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalid returns max u32")
# val id = ExprId.invalid()
# expect not id.is_valid()
expect true
```

</details>

### StmtId

#### creates valid statement id

- creates valid statement id


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates valid statement id")
# val id = StmtId.new(10)
# expect id.index == 10
# expect id.is_valid()
expect true
```

</details>

#### invalid returns max u32

- invalid returns max u32


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalid returns max u32")
# val id = StmtId.invalid()
# expect not id.is_valid()
expect true
```

</details>

### HirBody

#### creates empty body

- creates empty body


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty body")
# val body = HirBody.empty()
# expect body.local_count() == 0
# expect not body.root_stmt.is_valid()
expect true
```

</details>

#### creates body with root statement

- creates body with root statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates body with root statement")
# val root = StmtId.new(0)
# val body = HirBody.new(root)
# expect body.root_stmt.is_valid()
expect true
```

</details>

#### add_local increases count

- add_local increases count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_local increases count")
# var body = HirBody.empty()
# val local = LocalVar.new("x", TypeId.i64_ty(), false, 0)
# body.add_local(local)
# expect body.local_count() == 1
expect true
```

</details>

#### get_local returns correct local

- get_local returns correct local


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_local returns correct local")
# var body = HirBody.empty()
# body.add_local(LocalVar.new("x", TypeId.i64_ty(), false, 0))
# val local = body.get_local(0)
# expect local.is_some()
# expect local.unwrap().name == "x"
expect true
```

</details>

#### find_local finds by name

- find_local finds by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_local finds by name")
# var body = HirBody.empty()
# body.add_local(LocalVar.new("foo", TypeId.i64_ty(), false, 0))
# val local = body.find_local("foo")
# expect local.is_some()
expect true
```

</details>

### HirFunction Factory

#### creates function with signature

- creates function with signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates function with signature")
# val sig = HirFunctionSig.new("test", [], TypeId.void_ty())
# val func = HirFunction.new(0, sig)
# expect func.name() == "test"
# expect func.id == 0
expect true
```

</details>

#### creates function with body

- creates function with body


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates function with body")
# val sig = HirFunctionSig.new("test", [], TypeId.void_ty())
# val body = HirBody.empty()
# val func = HirFunction.with_body(0, sig, body)
# expect func.name() == "test"
expect true
```

</details>

### HirFunction Methods

#### name returns function name

- name returns function name


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("name returns function name")
# val sig = HirFunctionSig.new("my_func", [], TypeId.void_ty())
# val func = HirFunction.new(0, sig)
# expect func.name() == "my_func"
expect true
```

</details>

#### return_type returns correct type

- return_type returns correct type


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("return_type returns correct type")
# val sig = HirFunctionSig.new("foo", [], TypeId.i64_ty())
# val func = HirFunction.new(0, sig)
# expect func.return_type().id == TypeId.i64_ty().id
expect true
```

</details>

#### is_closure returns false for non-closure

- is_closure returns false for non-closure


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_closure returns false for non-closure")
# val sig = HirFunctionSig.new("foo", [], TypeId.void_ty())
# val func = HirFunction.new(0, sig)
# expect not func.is_closure()
expect true
```

</details>

#### is_closure returns true when captures present

- is_closure returns true when captures present


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_closure returns true when captures present")
# val sig = HirFunctionSig.new("foo", [], TypeId.void_ty())
# var func = HirFunction.new(0, sig)
# func.add_capture(CapturedVar.by_value(0))
# expect func.is_closure()
expect true
```

</details>

#### param_count delegates to signature

- param_count delegates to signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("param_count delegates to signature")
# val params = [HirParam.new("x", TypeId.i64_ty(), 0)]
# val sig = HirFunctionSig.new("foo", params, TypeId.void_ty())
# val func = HirFunction.new(0, sig)
# expect func.param_count() == 1
expect true
```

</details>

### TypeDefKind

#### Struct is_struct returns true

- Struct is_struct returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Struct is_struct returns true")
# expect TypeDefKind.Struct.is_struct()
expect true
```

</details>

#### Class is_class returns true

- Class is_class returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Class is_class returns true")
# expect TypeDefKind.Class.is_class()
expect true
```

</details>

#### Enum is_enum returns true

- Enum is_enum returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Enum is_enum returns true")
# expect TypeDefKind.Enum.is_enum()
expect true
```

</details>

#### Trait is_trait returns true

- Trait is_trait returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Trait is_trait returns true")
# expect TypeDefKind.Trait.is_trait()
expect true
```

</details>

#### to_string returns correct name

- to_string returns correct name


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_string returns correct name")
# expect TypeDefKind.Struct.to_string() == "struct"
# expect TypeDefKind.Class.to_string() == "class"
# expect TypeDefKind.Enum.to_string() == "enum"
expect true
```

</details>

### HirField

#### creates immutable field

- creates immutable field


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates immutable field")
# val field = HirField.new("x", TypeId.i64_ty(), 0)
# expect field.name == "x"
# expect field.index == 0
# expect field.is_mutable == false
expect true
```

</details>

#### creates mutable field

- creates mutable field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates mutable field")
# val field = HirField.mutable("x", TypeId.i64_ty(), 0)
# expect field.is_mutable == true
expect true
```

</details>

#### creates public field

- creates public field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates public field")
# val field = HirField.public("x", TypeId.i64_ty(), 0)
# expect field.visibility.is_public()
expect true
```

</details>

### HirVariant

#### creates unit variant

- creates unit variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates unit variant")
# val variant = HirVariant.unit("None", 0)
# expect variant.name == "None"
# expect variant.index == 0
# expect not variant.has_payload()
expect true
```

</details>

#### creates variant with payload

- creates variant with payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates variant with payload")
# val variant = HirVariant.with_payload("Some", 1, TypeId.i64_ty())
# expect variant.name == "Some"
# expect variant.has_payload()
expect true
```

</details>

### HirTypeDef Factory

#### creates struct definition

- creates struct definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates struct definition")
# val fields = [HirField.new("x", TypeId.i64_ty(), 0)]
# val def = HirTypeDef.struct_def(0, "Point", TypeId.i64_ty(), fields)
# expect def.name == "Point"
# expect def.kind.is_struct()
# expect def.field_count() == 1
expect true
```

</details>

#### creates class definition

- creates class definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates class definition")
# val fields = [HirField.new("count", TypeId.i64_ty(), 0)]
# val def = HirTypeDef.class_def(0, "Counter", TypeId.i64_ty(), fields)
# expect def.kind.is_class()
expect true
```

</details>

#### creates enum definition

- creates enum definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates enum definition")
# val variants = [HirVariant.unit("A", 0), HirVariant.unit("B", 1)]
# val def = HirTypeDef.enum_def(0, "MyEnum", TypeId.i64_ty(), variants)
# expect def.kind.is_enum()
# expect def.variant_count() == 2
expect true
```

</details>

### HirTypeDef Methods

#### find_field returns correct field

- find_field returns correct field


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_field returns correct field")
# val fields = [HirField.new("x", TypeId.i64_ty(), 0), HirField.new("y", TypeId.i64_ty(), 1)]
# val def = HirTypeDef.struct_def(0, "Point", TypeId.i64_ty(), fields)
# val field = def.find_field("y")
# expect field.is_some()
# expect field.unwrap().index == 1
expect true
```

</details>

#### find_variant returns correct variant

- find_variant returns correct variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_variant returns correct variant")
# val variants = [HirVariant.unit("A", 0), HirVariant.unit("B", 1)]
# val def = HirTypeDef.enum_def(0, "MyEnum", TypeId.i64_ty(), variants)
# val variant = def.find_variant("B")
# expect variant.is_some()
# expect variant.unwrap().index == 1
expect true
```

</details>

#### add_method adds method reference

- add_method adds method reference


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_method adds method reference")
# var def = HirTypeDef.struct_def(0, "Point", TypeId.i64_ty(), [])
# def.add_method(5)
# expect def.method_count() == 1
expect true
```

</details>

### HirImport

#### creates simple import

- creates simple import


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates simple import")
# val imp = HirImport.new("std.io", "File")
# expect imp.module_path == "std.io"
# expect imp.name == "File"
# expect imp.alias_name.is_none()
expect true
```

</details>

#### creates aliased import

- creates aliased import


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates aliased import")
# val imp = HirImport.aliased("std.io", "File", "F")
# expect imp.alias_name.is_some()
# expect imp.alias_name.unwrap() == "F"
expect true
```

</details>

#### creates wildcard import

- creates wildcard import


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates wildcard import")
# val imp = HirImport.wildcard("std.io")
# expect imp.is_wildcard
# expect imp.name == "*"
expect true
```

</details>

#### effective_name returns alias if present

- effective_name returns alias if present


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("effective_name returns alias if present")
# val imp = HirImport.aliased("std.io", "File", "F")
# expect imp.effective_name() == "F"
expect true
```

</details>

#### effective_name returns name if no alias

- effective_name returns name if no alias


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("effective_name returns name if no alias")
# val imp = HirImport.new("std.io", "File")
# expect imp.effective_name() == "File"
expect true
```

</details>

### HirModule Factory

#### creates empty module

- creates empty module


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty module")
# val mod = HirModule.new("main", "src/main.spl")
# expect mod.name == "main"
# expect mod.path == "src/main.spl"
# expect mod.function_count() == 0
expect true
```

</details>

### HirModule Methods

#### add_import adds import

- add_import adds import


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_import adds import")
# var mod = HirModule.new("main", "src/main.spl")
# mod.add_import(HirImport.new("std.io", "File"))
# expect mod.imports.len() == 1
expect true
```

</details>

#### add_function adds function

- add_function adds function


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_function adds function")
# var mod = HirModule.new("main", "src/main.spl")
# val sig = HirFunctionSig.new("main", [], TypeId.void_ty())
# mod.add_function(HirFunction.new(0, sig))
# expect mod.function_count() == 1
expect true
```

</details>

#### add_type adds type definition

- add_type adds type definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_type adds type definition")
# var mod = HirModule.new("main", "src/main.spl")
# val def = HirTypeDef.struct_def(0, "Point", TypeId.i64_ty(), [])
# mod.add_type(def)
# expect mod.type_count() == 1
expect true
```

</details>

#### find_function finds by name

- find_function finds by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_function finds by name")
# var mod = HirModule.new("main", "src/main.spl")
# val sig = HirFunctionSig.new("foo", [], TypeId.void_ty())
# mod.add_function(HirFunction.new(0, sig))
# val func = mod.find_function("foo")
# expect func.is_some()
expect true
```

</details>

#### find_type finds by name

- find_type finds by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_type finds by name")
# var mod = HirModule.new("main", "src/main.spl")
# val def = HirTypeDef.struct_def(0, "Point", TypeId.i64_ty(), [])
# mod.add_type(def)
# val type_def = mod.find_type("Point")
# expect type_def.is_some()
expect true
```

</details>

#### find_global finds by name

- find_global finds by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_global finds by name")
# var mod = HirModule.new("main", "src/main.spl")
# mod.add_global(LocalVar.new("VERSION", TypeId.string_ty(), false, 0))
# val global = mod.find_global("VERSION")
# expect global.is_some()
expect true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_module_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HirParam Factory Functions, Visibility, HirFunctionSig Factory, HirFunctionSig Methods, ExprId, StmtId, HirBody, HirFunction Factory, HirFunction Methods, TypeDefKind, HirField, HirVariant, HirTypeDef Factory, HirTypeDef Methods, HirImport, HirModule Factory, HirModule Methods.
- HirParam Factory Functions
- Visibility
- HirFunctionSig Factory
- HirFunctionSig Methods
- ExprId
- StmtId
- HirBody
- HirFunction Factory
- HirFunction Methods
- TypeDefKind
- HirField
- HirVariant
- HirTypeDef Factory
- HirTypeDef Methods
- HirImport
- HirModule Factory
- HirModule Methods

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 59 |
| Active scenarios | 59 |
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

- Canonical SPipe generation for source `9e7e21c3b3f9381eb10bdce85659c62dd5fab5c20f58a7567c1e13bc6133d593`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9e7e21c3b3f9381eb10bdce85659c62dd5fab5c20f58a7567c1e13bc6133d593`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9e7e21c3b3f9381eb10bdce85659c62dd5fab5c20f58a7567c1e13bc6133d593`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/hir_module_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_module_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/hir_module_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_module_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_module_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates immutable parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_module_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates mutable parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_module_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts to LocalVar' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
