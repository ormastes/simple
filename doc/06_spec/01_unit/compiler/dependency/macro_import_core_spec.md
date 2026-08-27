# Macro Import Core Specification

> Tests covering SymKind, MacroSymbol, AutoImport, MacroExports, MacroDirManifest.

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

- MacroKind is_macro returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MacroKind is_macro returns true")
val kind = SymKind.MacroKind
expect kind.is_macro()
```

</details>

#### ValueOrType is_macro returns false

- ValueOrType is_macro returns false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ValueOrType is_macro returns false")
val kind = SymKind.ValueOrType
expect not kind.is_macro()
```

</details>

#### to_string

#### MacroKind to_string

- MacroKind to_string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MacroKind to_string")
val kind = SymKind.MacroKind
expect kind.to_string() == "Macro"
```

</details>

#### ValueOrType to_string

- ValueOrType to_string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ValueOrType to_string")
val kind = SymKind.ValueOrType
expect kind.to_string() == "ValueOrType"
```

</details>

### MacroSymbol

#### construction

#### creates with explicit kind

- creates with explicit kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with explicit kind")
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

- value_sym creates ValueOrType


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("value_sym creates ValueOrType")
val sym = MacroSymbol.value_sym("mod", "bar")
val sym_kind = sym.get_kind()
expect not sym_kind.is_macro()
```

</details>

#### macro_sym creates MacroKind

- macro_sym creates MacroKind


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("macro_sym creates MacroKind")
val sym = MacroSymbol.macro_sym("mod", "my_macro")
val sym_kind = sym.get_kind()
expect sym_kind.is_macro()
```

</details>

#### getters

#### get_module_path returns module

- get_module_path returns module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_module_path returns module")
val sym = MacroSymbol.value_sym("test_mod", "foo")
expect sym.get_module_path() == "test_mod"
```

</details>

#### get_name returns name

- get_name returns name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_name returns name")
val sym = MacroSymbol.value_sym("mod", "test_name")
expect sym.get_name() == "test_name"
```

</details>

#### get_kind returns kind

- get_kind returns kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_kind returns kind")
val sym = MacroSymbol.macro_sym("mod", "foo")
val kind = sym.get_kind()
expect kind.is_macro()
```

</details>

#### equality

#### equal symbols

- equal symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("equal symbols")
val sym1 = MacroSymbol.value_sym("mod", "foo")
val sym2 = MacroSymbol.value_sym("mod", "foo")
expect sym1.equals(sym2)
```

</details>

#### different modules

- different modules


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different modules")
val sym1 = MacroSymbol.value_sym("mod1", "foo")
val sym2 = MacroSymbol.value_sym("mod2", "foo")
expect not sym1.equals(sym2)
```

</details>

#### different names

- different names


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different names")
val sym1 = MacroSymbol.value_sym("mod", "foo")
val sym2 = MacroSymbol.value_sym("mod", "bar")
expect not sym1.equals(sym2)
```

</details>

#### different kinds

- different kinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different kinds")
val sym1 = MacroSymbol.value_sym("mod", "foo")
val sym2 = MacroSymbol.macro_sym("mod", "foo")
expect not sym1.equals(sym2)
```

</details>

### AutoImport

#### construction

#### creates auto-import

- creates auto-import


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates auto-import")
val ai = AutoImport.new("mod", "my_macro")
val ai_module = ai.get_from_module()
val ai_macro = ai.get_macro_name()

expect ai_module == "mod"
expect ai_macro == "my_macro"
```

</details>

#### getters

#### get_from_module

- get_from_module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_from_module")
val ai = AutoImport.new("test_mod", "macro1")
expect ai.get_from_module() == "test_mod"
```

</details>

#### get_macro_name

- get_macro_name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_macro_name")
val ai = AutoImport.new("mod", "test_macro")
expect ai.get_macro_name() == "test_macro"
```

</details>

#### equality

#### equal auto-imports

- equal auto-imports


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("equal auto-imports")
val ai1 = AutoImport.new("mod", "macro1")
val ai2 = AutoImport.new("mod", "macro1")
expect ai1.equals(ai2)
```

</details>

#### different modules

- different modules


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different modules")
val ai1 = AutoImport.new("mod1", "macro1")
val ai2 = AutoImport.new("mod2", "macro1")
expect not ai1.equals(ai2)
```

</details>

#### different macro names

- different macro names


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different macro names")
val ai1 = AutoImport.new("mod", "macro1")
val ai2 = AutoImport.new("mod", "macro2")
expect not ai1.equals(ai2)
```

</details>

### MacroExports

#### construction

#### creates empty

- creates empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty")
val exports = MacroExports.new()
expect exports.non_macros.len() == 0
expect exports.macros.len() == 0
```

</details>

#### adding symbols

#### add_non_macro

- add_non_macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_non_macro")
var exports = MacroExports.new()
exports.add_non_macro(MacroSymbol.value_sym("mod", "foo"))
expect exports.non_macros.len() == 1
expect exports.macros.len() == 0
```

</details>

#### add_macro

- add_macro


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_macro")
var exports = MacroExports.new()
exports.add_macro(MacroSymbol.macro_sym("mod", "my_macro"))
expect exports.non_macros.len() == 0
expect exports.macros.len() == 1
```

</details>

#### add categorizes correctly

- add categorizes correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add categorizes correctly")
var exports = MacroExports.new()
exports.add(MacroSymbol.value_sym("mod", "foo"))
exports.add(MacroSymbol.macro_sym("mod", "my_macro"))

expect exports.non_macros.len() == 1
expect exports.macros.len() == 1
```

</details>

#### multiple non-macros

- multiple non-macros


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple non-macros")
var exports = MacroExports.new()
exports.add_non_macro(MacroSymbol.value_sym("mod", "foo"))
exports.add_non_macro(MacroSymbol.value_sym("mod", "bar"))
exports.add_non_macro(MacroSymbol.value_sym("mod", "baz"))
expect exports.non_macros.len() == 3
```

</details>

#### multiple macros

- multiple macros


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple macros")
var exports = MacroExports.new()
exports.add_macro(MacroSymbol.macro_sym("mod", "m1"))
exports.add_macro(MacroSymbol.macro_sym("mod", "m2"))
expect exports.macros.len() == 2
```

</details>

#### well-formedness

#### empty is well-formed

- empty is well-formed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty is well-formed")
val exports = MacroExports.new()
expect exports.is_well_formed()
```

</details>

#### only non-macros is well-formed

- only non-macros is well-formed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only non-macros is well-formed")
var exports = MacroExports.new()
exports.add_non_macro(MacroSymbol.value_sym("mod", "foo"))
exports.add_non_macro(MacroSymbol.value_sym("mod", "bar"))
expect exports.is_well_formed()
```

</details>

#### only macros is well-formed

- only macros is well-formed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only macros is well-formed")
var exports = MacroExports.new()
exports.add_macro(MacroSymbol.macro_sym("mod", "m1"))
exports.add_macro(MacroSymbol.macro_sym("mod", "m2"))
expect exports.is_well_formed()
```

</details>

#### mixed is well-formed

- mixed is well-formed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mixed is well-formed")
var exports = MacroExports.new()
exports.add_non_macro(MacroSymbol.value_sym("mod", "foo"))
exports.add_macro(MacroSymbol.macro_sym("mod", "my_macro"))
expect exports.is_well_formed()
```

</details>

#### macro in non-macros is not well-formed

- macro in non-macros is not well-formed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("macro in non-macros is not well-formed")
var exports = MacroExports.new()
exports.non_macros.push(MacroSymbol.macro_sym("mod", "bad"))
expect not exports.is_well_formed()
```

</details>

#### value in macros is not well-formed

- value in macros is not well-formed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("value in macros is not well-formed")
var exports = MacroExports.new()
exports.macros.push(MacroSymbol.value_sym("mod", "bad"))
expect not exports.is_well_formed()
```

</details>

### MacroDirManifest

#### construction

#### creates empty

- creates empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty")
val manifest = MacroDirManifest.new("test")
expect manifest.name == "test"
expect manifest.auto_imports.len() == 0
```

</details>

#### preserves name

- preserves name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves name")
val manifest = MacroDirManifest.new("my_directory")
expect manifest.name == "my_directory"
```

</details>

#### adding auto-imports

#### add_auto_import single

- add_auto_import single


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_auto_import single")
var manifest = MacroDirManifest.new("test")
manifest.add_auto_import(AutoImport.new("mod", "my_macro"))
expect manifest.auto_imports.len() == 1
```

</details>

#### add_auto_import multiple

- add_auto_import multiple


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_auto_import multiple")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SymKind, MacroSymbol, AutoImport, MacroExports, MacroDirManifest.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fec779217155223c9ea15ce113c1ca60bba14c78e0980d7510421b15cb437104`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fec779217155223c9ea15ce113c1ca60bba14c78e0980d7510421b15cb437104`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fec779217155223c9ea15ce113c1ca60bba14c78e0980d7510421b15cb437104`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/dependency/macro_import_core_spec.spl
mirror: doc/06_spec/01_unit/compiler/dependency/macro_import_core_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/dependency/macro_import_core_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/dependency/macro_import_core_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/dependency/macro_import_core_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'MacroKind is_macro returns true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/dependency/macro_import_core_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ValueOrType is_macro returns false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/dependency/macro_import_core_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'MacroKind to_string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
