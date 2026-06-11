# Macro Import Core Specification

> 1. expect kind is macro

<!-- sdn-diagram:id=macro_import_core_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_import_core_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_import_core_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_import_core_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macro Import Core Specification

## Scenarios

### SymKind

#### predicates

#### MacroKind is_macro returns true

1. expect kind is macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = SymKind.MacroKind
expect kind.is_macro()
```

</details>

#### ValueOrType is_macro returns false

1. expect not kind is macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = SymKind.ValueOrType
expect not kind.is_macro()
```

</details>

#### to_string

#### MacroKind to_string

1. expect kind to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = SymKind.MacroKind
expect kind.to_string() == "Macro"
```

</details>

#### ValueOrType to_string

1. expect kind to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = SymKind.ValueOrType
expect kind.to_string() == "ValueOrType"
```

</details>

### MacroSymbol

#### construction

#### creates with explicit kind

1. expect not sym kind is macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym = MacroSymbol.new("mod", "foo", SymKind.ValueOrType)
val sym_module = sym.get_module_path()
val sym_name = sym.get_name()
val sym_kind = sym.get_kind()

expect sym_module == "mod"
expect sym_name == "foo"
expect not sym_kind.is_macro()
```

</details>

#### value_sym creates ValueOrType

1. expect not sym kind is macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym = MacroSymbol.value_sym("mod", "bar")
val sym_kind = sym.get_kind()
expect not sym_kind.is_macro()
```

</details>

#### macro_sym creates MacroKind

1. expect sym kind is macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym = MacroSymbol.macro_sym("mod", "my_macro")
val sym_kind = sym.get_kind()
expect sym_kind.is_macro()
```

</details>

#### getters

#### get_module_path returns module

1. expect sym get module path


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym = MacroSymbol.value_sym("test_mod", "foo")
expect sym.get_module_path() == "test_mod"
```

</details>

#### get_name returns name

1. expect sym get name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym = MacroSymbol.value_sym("mod", "test_name")
expect sym.get_name() == "test_name"
```

</details>

#### get_kind returns kind

1. expect kind is macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym = MacroSymbol.macro_sym("mod", "foo")
val kind = sym.get_kind()
expect kind.is_macro()
```

</details>

#### equality

#### equal symbols

1. expect sym1 equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym1 = MacroSymbol.value_sym("mod", "foo")
val sym2 = MacroSymbol.value_sym("mod", "foo")
expect sym1.equals(sym2)
```

</details>

#### different modules

1. expect not sym1 equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym1 = MacroSymbol.value_sym("mod1", "foo")
val sym2 = MacroSymbol.value_sym("mod2", "foo")
expect not sym1.equals(sym2)
```

</details>

#### different names

1. expect not sym1 equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym1 = MacroSymbol.value_sym("mod", "foo")
val sym2 = MacroSymbol.value_sym("mod", "bar")
expect not sym1.equals(sym2)
```

</details>

#### different kinds

1. expect not sym1 equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym1 = MacroSymbol.value_sym("mod", "foo")
val sym2 = MacroSymbol.macro_sym("mod", "foo")
expect not sym1.equals(sym2)
```

</details>

### AutoImport

#### construction

#### creates auto-import

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ai = AutoImport.new("mod", "my_macro")
val ai_module = ai.get_from_module()
val ai_macro = ai.get_macro_name()

expect ai_module == "mod"
expect ai_macro == "my_macro"
```

</details>

#### getters

#### get_from_module

1. expect ai get from module


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ai = AutoImport.new("test_mod", "macro1")
expect ai.get_from_module() == "test_mod"
```

</details>

#### get_macro_name

1. expect ai get macro name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ai = AutoImport.new("mod", "test_macro")
expect ai.get_macro_name() == "test_macro"
```

</details>

#### equality

#### equal auto-imports

1. expect ai1 equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ai1 = AutoImport.new("mod", "macro1")
val ai2 = AutoImport.new("mod", "macro1")
expect ai1.equals(ai2)
```

</details>

#### different modules

1. expect not ai1 equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ai1 = AutoImport.new("mod1", "macro1")
val ai2 = AutoImport.new("mod2", "macro1")
expect not ai1.equals(ai2)
```

</details>

#### different macro names

1. expect not ai1 equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ai1 = AutoImport.new("mod", "macro1")
val ai2 = AutoImport.new("mod", "macro2")
expect not ai1.equals(ai2)
```

</details>

### MacroExports

#### construction

#### creates empty

1. expect exports non macros len
2. expect exports macros len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = MacroExports.new()
expect exports.non_macros.len() == 0
expect exports.macros.len() == 0
```

</details>

#### adding symbols

#### add_non_macro

1. var exports = MacroExports new
2. exports add non macro
3. expect exports non macros len
4. expect exports macros len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exports = MacroExports.new()
exports.add_non_macro(MacroSymbol.value_sym("mod", "foo"))
expect exports.non_macros.len() == 1
expect exports.macros.len() == 0
```

</details>

#### add_macro

1. var exports = MacroExports new
2. exports add macro
3. expect exports non macros len
4. expect exports macros len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exports = MacroExports.new()
exports.add_macro(MacroSymbol.macro_sym("mod", "my_macro"))
expect exports.non_macros.len() == 0
expect exports.macros.len() == 1
```

</details>

#### add categorizes correctly

1. var exports = MacroExports new
2. exports add
3. exports add
4. expect exports non macros len
5. expect exports macros len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exports = MacroExports.new()
exports.add(MacroSymbol.value_sym("mod", "foo"))
exports.add(MacroSymbol.macro_sym("mod", "my_macro"))

expect exports.non_macros.len() == 1
expect exports.macros.len() == 1
```

</details>

#### multiple non-macros

1. var exports = MacroExports new
2. exports add non macro
3. exports add non macro
4. exports add non macro
5. expect exports non macros len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exports = MacroExports.new()
exports.add_non_macro(MacroSymbol.value_sym("mod", "foo"))
exports.add_non_macro(MacroSymbol.value_sym("mod", "bar"))
exports.add_non_macro(MacroSymbol.value_sym("mod", "baz"))
expect exports.non_macros.len() == 3
```

</details>

#### multiple macros

1. var exports = MacroExports new
2. exports add macro
3. exports add macro
4. expect exports macros len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exports = MacroExports.new()
exports.add_macro(MacroSymbol.macro_sym("mod", "m1"))
exports.add_macro(MacroSymbol.macro_sym("mod", "m2"))
expect exports.macros.len() == 2
```

</details>

#### well-formedness

#### empty is well-formed

1. expect exports is well formed


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = MacroExports.new()
expect exports.is_well_formed()
```

</details>

#### only non-macros is well-formed

1. var exports = MacroExports new
2. exports add non macro
3. exports add non macro
4. expect exports is well formed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exports = MacroExports.new()
exports.add_non_macro(MacroSymbol.value_sym("mod", "foo"))
exports.add_non_macro(MacroSymbol.value_sym("mod", "bar"))
expect exports.is_well_formed()
```

</details>

#### only macros is well-formed

1. var exports = MacroExports new
2. exports add macro
3. exports add macro
4. expect exports is well formed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exports = MacroExports.new()
exports.add_macro(MacroSymbol.macro_sym("mod", "m1"))
exports.add_macro(MacroSymbol.macro_sym("mod", "m2"))
expect exports.is_well_formed()
```

</details>

#### mixed is well-formed

1. var exports = MacroExports new
2. exports add non macro
3. exports add macro
4. expect exports is well formed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exports = MacroExports.new()
exports.add_non_macro(MacroSymbol.value_sym("mod", "foo"))
exports.add_macro(MacroSymbol.macro_sym("mod", "my_macro"))
expect exports.is_well_formed()
```

</details>

#### macro in non-macros is not well-formed

1. var exports = MacroExports new
2. exports non macros push
3. expect not exports is well formed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exports = MacroExports.new()
exports.non_macros.push(MacroSymbol.macro_sym("mod", "bad"))
expect not exports.is_well_formed()
```

</details>

#### value in macros is not well-formed

1. var exports = MacroExports new
2. exports macros push
3. expect not exports is well formed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exports = MacroExports.new()
exports.macros.push(MacroSymbol.value_sym("mod", "bad"))
expect not exports.is_well_formed()
```

</details>

### MacroDirManifest

#### construction

#### creates empty

1. expect manifest auto imports len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = MacroDirManifest.new("test")
expect manifest.name == "test"
expect manifest.auto_imports.len() == 0
```

</details>

#### preserves name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = MacroDirManifest.new("my_directory")
expect manifest.name == "my_directory"
```

</details>

#### adding auto-imports

#### add_auto_import single

1. var manifest = MacroDirManifest new
2. manifest add auto import
3. expect manifest auto imports len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "my_macro"))
expect manifest.auto_imports.len() == 1
```

</details>

#### add_auto_import multiple

1. var manifest = MacroDirManifest new
2. manifest add auto import
3. manifest add auto import
4. manifest add auto import
5. expect manifest auto imports len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod1", "macro1"))
manifest.add_auto_import(AutoImport.new("mod2", "macro2"))
manifest.add_auto_import(AutoImport.new("mod3", "macro3"))
expect manifest.auto_imports.len() == 3
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/dependency/macro_import_core_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SymKind
- MacroSymbol
- AutoImport
- MacroExports
- MacroDirManifest

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
