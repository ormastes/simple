# Macro Import Algorithms Specification

> Tests covering is_auto_imported, auto_imported_macros, glob_import, explicit_import, combine_exports.

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

- finds macro in list


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds macro in list")
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "my_macro"))

val sym = MacroSymbol.macro_sym("mod", "my_macro")
expect is_auto_imported(manifest, sym)
```

</details>

#### not found returns false

- not found returns false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("not found returns false")
val manifest = MacroDirManifest.new("test")
val sym = MacroSymbol.macro_sym("mod", "my_macro")
expect not is_auto_imported(manifest, sym)
```

</details>

#### wrong module returns false

- wrong module returns false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wrong module returns false")
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod1", "my_macro"))

val sym = MacroSymbol.macro_sym("mod2", "my_macro")
expect not is_auto_imported(manifest, sym)
```

</details>

#### wrong name returns false

- wrong name returns false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wrong name returns false")
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "macro1"))

val sym = MacroSymbol.macro_sym("mod", "macro2")
expect not is_auto_imported(manifest, sym)
```

</details>

#### kind checking

#### non-macro always returns false

- non-macro always returns false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-macro always returns false")
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "foo"))

val sym = MacroSymbol.value_sym("mod", "foo")
expect not is_auto_imported(manifest, sym)
```

</details>

#### value type with macro name in list

- value type with macro name in list


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("value type with macro name in list")
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "my_name"))

val sym = MacroSymbol.value_sym("mod", "my_name")
expect not is_auto_imported(manifest, sym)
```

</details>

#### multiple imports

#### finds first in list

- finds first in list


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds first in list")
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "macro1"))
manifest.add_auto_import(AutoImport.new("mod", "macro2"))

val sym = MacroSymbol.macro_sym("mod", "macro1")
expect is_auto_imported(manifest, sym)
```

</details>

#### finds last in list

- finds last in list


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds last in list")
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "macro1"))
manifest.add_auto_import(AutoImport.new("mod", "macro2"))

val sym = MacroSymbol.macro_sym("mod", "macro2")
expect is_auto_imported(manifest, sym)
```

</details>

#### finds middle in list

- finds middle in list


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds middle in list")
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

- empty exports


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty exports")
val exports = MacroExports.new()
val manifest = MacroDirManifest.new("test")

val result = auto_imported_macros(manifest, exports)
expect result.len() == 0
```

</details>

#### empty auto-imports

- empty auto-imports


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty auto-imports")
val exports = make_exports()
val manifest = MacroDirManifest.new("test")

val result = auto_imported_macros(manifest, exports)
expect result.len() == 0
```

</details>

#### no macros in exports

- no macros in exports


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no macros in exports")
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

- returns single auto-imported macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns single auto-imported macro")
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

- returns multiple auto-imported macros


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns multiple auto-imported macros")
val exports = make_exports()
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "my_macro"))
manifest.add_auto_import(AutoImport.new("mod", "other_macro"))

val result = auto_imported_macros(manifest, exports)
expect result.len() == 2
```

</details>

#### filters out non-auto-imported

- filters out non-auto-imported


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters out non-auto-imported")
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

- all non-macros present


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all non-macros present")
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

- counts non-macros correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts non-macros correctly")
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

- includes single auto-imported


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes single auto-imported")
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

- includes all auto-imported


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes all auto-imported")
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

- excludes when none auto-imported


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excludes when none auto-imported")
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

- excludes specific non-auto-imported


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excludes specific non-auto-imported")
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

- finds non-macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds non-macro")
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

- finds macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds macro")
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

- finds all non-macros


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds all non-macros")
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

- finds all macros


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds all macros")
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

- returns None for non-existent


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None for non-existent")
val exports = make_exports()
match explicit_import(exports, "nonexistent"):
    case Some(_):
        fail("Expected None")
    case nil:
        pass
```

</details>

#### returns None for empty exports

- returns None for empty exports


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None for empty exports")
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

- both empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("both empty")
val e1 = MacroExports.new()
val e2 = MacroExports.new()

val combined = combine_exports(e1, e2)
expect combined.non_macros.len() == 0
expect combined.macros.len() == 0
```

</details>

#### first empty

- first empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first empty")
val e1 = MacroExports.new()
var e2 = MacroExports.new()
e2.add_non_macro(MacroSymbol.value_sym("mod", "foo"))

val combined = combine_exports(e1, e2)
expect combined.non_macros.len() == 1
```

</details>

#### second empty

- second empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("second empty")
var e1 = MacroExports.new()
e1.add_non_macro(MacroSymbol.value_sym("mod", "foo"))
val e2 = MacroExports.new()

val combined = combine_exports(e1, e2)
expect combined.non_macros.len() == 1
```

</details>

#### combining non-macros

#### combines from both

- combines from both


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines from both")
var e1 = MacroExports.new()
e1.add_non_macro(MacroSymbol.value_sym("mod1", "foo"))

var e2 = MacroExports.new()
e2.add_non_macro(MacroSymbol.value_sym("mod2", "bar"))

val combined = combine_exports(e1, e2)
expect combined.non_macros.len() == 2
```

</details>

#### preserves all non-macros

- preserves all non-macros


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves all non-macros")
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

- combines from both


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines from both")
var e1 = MacroExports.new()
e1.add_macro(MacroSymbol.macro_sym("mod1", "macro1"))

var e2 = MacroExports.new()
e2.add_macro(MacroSymbol.macro_sym("mod2", "macro2"))

val combined = combine_exports(e1, e2)
expect combined.macros.len() == 2
```

</details>

#### preserves all macros

- preserves all macros


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves all macros")
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

- combines non-macros and macros


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines non-macros and macros")
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
| Source | `test/unit/compiler/dependency/macro_import_algorithms_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering is_auto_imported, auto_imported_macros, glob_import, explicit_import, combine_exports.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c885bbe6c64dbb60dbb8b1ce61b5d0af898ac98921e80951906d93ae909bb947`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c885bbe6c64dbb60dbb8b1ce61b5d0af898ac98921e80951906d93ae909bb947`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c885bbe6c64dbb60dbb8b1ce61b5d0af898ac98921e80951906d93ae909bb947`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/dependency/macro_import_algorithms_spec.spl
mirror: doc/06_spec/unit/compiler/dependency/macro_import_algorithms_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/dependency/macro_import_algorithms_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/dependency/macro_import_algorithms_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/dependency/macro_import_algorithms_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds macro in list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/dependency/macro_import_algorithms_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'not found returns false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/dependency/macro_import_algorithms_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wrong module returns false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
