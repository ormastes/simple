# Macro Import Algorithms Specification

> 1. var manifest = MacroDirManifest new

<!-- sdn-diagram:id=macro_import_algorithms_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_import_algorithms_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_import_algorithms_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_import_algorithms_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macro Import Algorithms Specification

## Scenarios

### is_auto_imported

#### basic functionality

#### finds macro in list

1. var manifest = MacroDirManifest new
2. manifest add auto import
3. expect is auto imported


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "my_macro"))

val sym = MacroSymbol.macro_sym("mod", "my_macro")
expect is_auto_imported(manifest, sym)
```

</details>

#### not found returns false

1. expect not is auto imported


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = MacroDirManifest.new("test")
val sym = MacroSymbol.macro_sym("mod", "my_macro")
expect not is_auto_imported(manifest, sym)
```

</details>

#### wrong module returns false

1. var manifest = MacroDirManifest new
2. manifest add auto import
3. expect not is auto imported


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod1", "my_macro"))

val sym = MacroSymbol.macro_sym("mod2", "my_macro")
expect not is_auto_imported(manifest, sym)
```

</details>

#### wrong name returns false

1. var manifest = MacroDirManifest new
2. manifest add auto import
3. expect not is auto imported


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "macro1"))

val sym = MacroSymbol.macro_sym("mod", "macro2")
expect not is_auto_imported(manifest, sym)
```

</details>

#### kind checking

#### non-macro always returns false

1. var manifest = MacroDirManifest new
2. manifest add auto import
3. expect not is auto imported


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "foo"))

val sym = MacroSymbol.value_sym("mod", "foo")
expect not is_auto_imported(manifest, sym)
```

</details>

#### value type with macro name in list

1. var manifest = MacroDirManifest new
2. manifest add auto import
3. expect not is auto imported


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "my_name"))

val sym = MacroSymbol.value_sym("mod", "my_name")
expect not is_auto_imported(manifest, sym)
```

</details>

#### multiple imports

#### finds first in list

1. var manifest = MacroDirManifest new
2. manifest add auto import
3. manifest add auto import
4. expect is auto imported


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "macro1"))
manifest.add_auto_import(AutoImport.new("mod", "macro2"))

val sym = MacroSymbol.macro_sym("mod", "macro1")
expect is_auto_imported(manifest, sym)
```

</details>

#### finds last in list

1. var manifest = MacroDirManifest new
2. manifest add auto import
3. manifest add auto import
4. expect is auto imported


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "macro1"))
manifest.add_auto_import(AutoImport.new("mod", "macro2"))

val sym = MacroSymbol.macro_sym("mod", "macro2")
expect is_auto_imported(manifest, sym)
```

</details>

#### finds middle in list

1. var manifest = MacroDirManifest new
2. manifest add auto import
3. manifest add auto import
4. manifest add auto import
5. expect is auto imported


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "macro1"))
manifest.add_auto_import(AutoImport.new("mod", "macro2"))
manifest.add_auto_import(AutoImport.new("mod", "macro3"))

val sym = MacroSymbol.macro_sym("mod", "macro2")
expect is_auto_imported(manifest, sym)
```

</details>

### auto_imported_macros

#### empty cases

#### empty exports

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = MacroExports.new()
val manifest = MacroDirManifest.new("test")

val result = auto_imported_macros(manifest, exports)
expect result.len() == 0
```

</details>

#### empty auto-imports

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = make_exports()
val manifest = MacroDirManifest.new("test")

val result = auto_imported_macros(manifest, exports)
expect result.len() == 0
```

</details>

#### no macros in exports

1. var exports = MacroExports new
2. exports add non macro
3. var manifest = MacroDirManifest new
4. manifest add auto import
5. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var exports = MacroExports.new()
exports.add_non_macro(MacroSymbol.value_sym("mod", "foo"))

var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "foo"))

val result = auto_imported_macros(manifest, exports)
expect result.len() == 0
```

</details>

#### filtering

#### returns single auto-imported macro

1. var manifest = MacroDirManifest new
2. manifest add auto import
3. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = make_exports()
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "my_macro"))

val result = auto_imported_macros(manifest, exports)
expect result.len() == 1

if result.len() > 0:
    val first_sym = result[0]
    val first_name = first_sym.get_name()
    expect first_name == "my_macro"
```

</details>

#### returns multiple auto-imported macros

1. var manifest = MacroDirManifest new
2. manifest add auto import
3. manifest add auto import
4. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = make_exports()
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "my_macro"))
manifest.add_auto_import(AutoImport.new("mod", "other_macro"))

val result = auto_imported_macros(manifest, exports)
expect result.len() == 2
```

</details>

#### filters out non-auto-imported

1. var manifest = MacroDirManifest new
2. manifest add auto import


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = make_exports()
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "my_macro"))

val result = auto_imported_macros(manifest, exports)

# Should not include other_macro
var found_other = false
for sym in result:
    val sym_name = sym.get_name()
    if sym_name == "other_macro":
        found_other = true

expect not found_other
```

</details>

### glob_import

#### includes non-macros

#### all non-macros present

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = make_exports()
val manifest = MacroDirManifest.new("test")

val result = glob_import(manifest, exports)

var found_foo = false
var found_bar = false
for sym in result:
    val sym_name = sym.get_name()
    if sym_name == "foo":
        found_foo = true
    if sym_name == "bar":
        found_bar = true

expect found_foo
expect found_bar
```

</details>

#### counts non-macros correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = make_exports()
val manifest = MacroDirManifest.new("test")

val result = glob_import(manifest, exports)

var non_macro_count = 0
for sym in result:
    val sym_kind = sym.get_kind()
    if not sym_kind.is_macro():
        non_macro_count = non_macro_count + 1

expect non_macro_count == 2
```

</details>

#### includes auto-imported macros

#### includes single auto-imported

1. var manifest = MacroDirManifest new
2. manifest add auto import


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = make_exports()
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "my_macro"))

val result = glob_import(manifest, exports)

var found = false
for sym in result:
    val sym_name = sym.get_name()
    if sym_name == "my_macro":
        found = true

expect found
```

</details>

#### includes all auto-imported

1. var manifest = MacroDirManifest new
2. manifest add auto import
3. manifest add auto import


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = make_exports()
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "my_macro"))
manifest.add_auto_import(AutoImport.new("mod", "other_macro"))

val result = glob_import(manifest, exports)

var found_my = false
var found_other = false
for sym in result:
    val sym_name = sym.get_name()
    if sym_name == "my_macro":
        found_my = true
    if sym_name == "other_macro":
        found_other = true

expect found_my
expect found_other
```

</details>

#### excludes non-auto-imported macros

#### excludes when none auto-imported

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = make_exports()
val manifest = MacroDirManifest.new("test")

val result = glob_import(manifest, exports)

var found_any_macro = false
for sym in result:
    val sym_kind = sym.get_kind()
    if sym_kind.is_macro():
        found_any_macro = true

expect not found_any_macro
```

</details>

#### excludes specific non-auto-imported

1. var manifest = MacroDirManifest new
2. manifest add auto import


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = make_exports()
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "my_macro"))

val result = glob_import(manifest, exports)

var found_other = false
for sym in result:
    val sym_name = sym.get_name()
    if sym_name == "other_macro":
        found_other = true

expect not found_other
```

</details>

### explicit_import

#### finding symbols

#### finds non-macro

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = make_exports()
match explicit_import(exports, "foo"):
    case Some(sym):
        val sym_name = sym.get_name()
        expect sym_name == "foo"
    case nil:
        fail("Expected Some(symbol)")
```

</details>

#### finds macro

1. expect sym kind is macro
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = make_exports()
match explicit_import(exports, "my_macro"):
    case Some(sym):
        val sym_name = sym.get_name()
        val sym_kind = sym.get_kind()
        expect sym_name == "my_macro"
        expect sym_kind.is_macro()
    case nil:
        fail("Expected Some(symbol)")
```

</details>

#### finds all non-macros

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = make_exports()
match explicit_import(exports, "bar"):
    case Some(sym):
        val sym_name = sym.get_name()
        expect sym_name == "bar"
    case nil:
        fail("Expected Some(symbol)")
```

</details>

#### finds all macros

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = make_exports()
match explicit_import(exports, "other_macro"):
    case Some(sym):
        val sym_name = sym.get_name()
        expect sym_name == "other_macro"
    case nil:
        fail("Expected Some(symbol)")
```

</details>

#### not found

#### returns None for non-existent

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = make_exports()
match explicit_import(exports, "nonexistent"):
    case Some(_):
        fail("Expected None")
    case nil:
        pass
```

</details>

#### returns None for empty exports

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exports = MacroExports.new()
match explicit_import(exports, "anything"):
    case Some(_):
        fail("Expected None")
    case nil:
        pass
```

</details>

### combine_exports

#### empty combinations

#### both empty

1. expect combined non macros len
2. expect combined macros len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e1 = MacroExports.new()
val e2 = MacroExports.new()

val combined = combine_exports(e1, e2)
expect combined.non_macros.len() == 0
expect combined.macros.len() == 0
```

</details>

#### first empty

1. var e2 = MacroExports new
2. e2 add non macro
3. expect combined non macros len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e1 = MacroExports.new()
var e2 = MacroExports.new()
e2.add_non_macro(MacroSymbol.value_sym("mod", "foo"))

val combined = combine_exports(e1, e2)
expect combined.non_macros.len() == 1
```

</details>

#### second empty

1. var e1 = MacroExports new
2. e1 add non macro
3. expect combined non macros len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e1 = MacroExports.new()
e1.add_non_macro(MacroSymbol.value_sym("mod", "foo"))
val e2 = MacroExports.new()

val combined = combine_exports(e1, e2)
expect combined.non_macros.len() == 1
```

</details>

#### combining non-macros

#### combines from both

1. var e1 = MacroExports new
2. e1 add non macro
3. var e2 = MacroExports new
4. e2 add non macro
5. expect combined non macros len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e1 = MacroExports.new()
e1.add_non_macro(MacroSymbol.value_sym("mod1", "foo"))

var e2 = MacroExports.new()
e2.add_non_macro(MacroSymbol.value_sym("mod2", "bar"))

val combined = combine_exports(e1, e2)
expect combined.non_macros.len() == 2
```

</details>

#### preserves all non-macros

1. var e1 = MacroExports new
2. e1 add non macro
3. e1 add non macro
4. var e2 = MacroExports new
5. e2 add non macro
6. expect combined non macros len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e1 = MacroExports.new()
e1.add_non_macro(MacroSymbol.value_sym("mod1", "foo"))
e1.add_non_macro(MacroSymbol.value_sym("mod1", "bar"))

var e2 = MacroExports.new()
e2.add_non_macro(MacroSymbol.value_sym("mod2", "baz"))

val combined = combine_exports(e1, e2)
expect combined.non_macros.len() == 3
```

</details>

#### combining macros

#### combines from both

1. var e1 = MacroExports new
2. e1 add macro
3. var e2 = MacroExports new
4. e2 add macro
5. expect combined macros len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e1 = MacroExports.new()
e1.add_macro(MacroSymbol.macro_sym("mod1", "macro1"))

var e2 = MacroExports.new()
e2.add_macro(MacroSymbol.macro_sym("mod2", "macro2"))

val combined = combine_exports(e1, e2)
expect combined.macros.len() == 2
```

</details>

#### preserves all macros

1. var e1 = MacroExports new
2. e1 add macro
3. e1 add macro
4. var e2 = MacroExports new
5. e2 add macro
6. expect combined macros len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e1 = MacroExports.new()
e1.add_macro(MacroSymbol.macro_sym("mod1", "m1"))
e1.add_macro(MacroSymbol.macro_sym("mod1", "m2"))

var e2 = MacroExports.new()
e2.add_macro(MacroSymbol.macro_sym("mod2", "m3"))

val combined = combine_exports(e1, e2)
expect combined.macros.len() == 3
```

</details>

#### mixed combinations

#### combines non-macros and macros

1. var e1 = MacroExports new
2. e1 add non macro
3. e1 add macro
4. var e2 = MacroExports new
5. e2 add non macro
6. e2 add macro
7. expect combined non macros len
8. expect combined macros len


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e1 = MacroExports.new()
e1.add_non_macro(MacroSymbol.value_sym("mod1", "foo"))
e1.add_macro(MacroSymbol.macro_sym("mod1", "m1"))

var e2 = MacroExports.new()
e2.add_non_macro(MacroSymbol.value_sym("mod2", "bar"))
e2.add_macro(MacroSymbol.macro_sym("mod2", "m2"))

val combined = combine_exports(e1, e2)
expect combined.non_macros.len() == 2
expect combined.macros.len() == 2
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/dependency/macro_import_algorithms_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- is_auto_imported
- auto_imported_macros
- glob_import
- explicit_import
- combine_exports

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
