# Import C Defines Specification

> Tests covering import_c defines — system config forwarding, import_c defines — preprocessor conditionals, import_c defines — #define collection, import_c defines — macro expansion, import_c defines — include processing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Import C Defines Specification

## Scenarios

### import_c defines — system config forwarding

#### preprocessor accepts initial_defines parameter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preprocessor accepts initial_defines parameter
   - Expected: src contains `initial_defines: {text: text}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preprocessor accepts initial_defines parameter")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("initial_defines: {text: text}")).to_equal(true)
```

</details>

#### initial defines are copied into active define table

- initial defines are copied into active define table
   - Expected: src contains `defines[key] = initial_defines[key]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("initial defines are copied into active define table")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("defines[key] = initial_defines[key]")).to_equal(true)
```

</details>

#### CImportDefine carries name and value for forwarding

- CImportDefine carries name and value for forwarding
   - Expected: src contains `struct CImportDefine:`
   - Expected: src contains `name: text`
   - Expected: src contains `value: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("CImportDefine carries name and value for forwarding")
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("struct CImportDefine:")).to_equal(true)
expect(src.contains("name: text")).to_equal(true)
expect(src.contains("value: text")).to_equal(true)
```

</details>

#### build_define_map converts CImportDefine list to map

- build_define_map converts CImportDefine list to map
   - Expected: src contains `fn build_define_map(forwards: [CImportDefine]) -> {text: text}`
   - Expected: src contains `result[fwd.name] = fwd.value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("build_define_map converts CImportDefine list to map")
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("fn build_define_map(forwards: [CImportDefine]) -> {text: text}")).to_equal(true)
expect(src.contains("result[fwd.name] = fwd.value")).to_equal(true)
```

</details>

### import_c defines — preprocessor conditionals

#### handles #ifdef with define table lookup

- handles #ifdef with define table lookup
   - Expected: src contains `defines.contains_key(directive_arg.trim())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles #ifdef with define table lookup")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("defines.contains_key(directive_arg.trim())")).to_equal(true)
```

</details>

#### handles #ifndef as inverse of #ifdef

- handles #ifndef as inverse of #ifdef
   - Expected: src contains `directive == "ifndef"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles #ifndef as inverse of #ifdef")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("directive == \"ifndef\"")).to_equal(true)
```

</details>

#### handles nested #if with skip_depth tracking

- handles nested #if with skip_depth tracking
   - Expected: src contains `skip_depth`
   - Expected: src contains `condition_stack`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles nested #if with skip_depth tracking")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("skip_depth")).to_equal(true)
expect(src.contains("condition_stack")).to_equal(true)
```

</details>

#### evaluates defined() in #if conditions

- evaluates defined() in #if conditions
   - Expected: src contains `fn pp_eval_condition`
   - Expected: src contains `defines.contains_key(name)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates defined() in #if conditions")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("fn pp_eval_condition")).to_equal(true)
expect(src.contains("defines.contains_key(name)")).to_equal(true)
```

</details>

### import_c defines — #define collection

#### collects defines during preprocessing

- collects defines during preprocessing
   - Expected: src contains `collected_defines`
   - Expected: src contains `collected_defines.push`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collects defines during preprocessing")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("collected_defines")).to_equal(true)
expect(src.contains("collected_defines.push")).to_equal(true)
```

</details>

#### pp_make_c_define detects integer values

- pp_make_c_define detects integer values
   - Expected: src contains `fn pp_make_c_define`
   - Expected: src contains `is_int = true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pp_make_c_define detects integer values")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("fn pp_make_c_define")).to_equal(true)
expect(src.contains("is_int = true")).to_equal(true)
```

</details>

#### pp_parse_define extracts name and value

- pp_parse_define extracts name and value
   - Expected: src contains `fn pp_parse_define`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pp_parse_define extracts name and value")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("fn pp_parse_define")).to_equal(true)
```

</details>

#### handles function-like macros by skipping parenthesized params

- handles function-like macros by skipping parenthesized params
   - Expected: src contains `trimmed[i] == "("`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles function-like macros by skipping parenthesized params")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("trimmed[i] == \"(\"")).to_equal(true)
```

</details>

### import_c defines — macro expansion

#### expands defines as whole-word identifiers

- expands defines as whole-word identifiers
   - Expected: src contains `fn pp_replace_ident`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expands defines as whole-word identifiers")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("fn pp_replace_ident")).to_equal(true)
```

</details>

#### checks word boundaries before and after match

- checks word boundaries before and after match
   - Expected: src contains `before_ok`
   - Expected: src contains `after_ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks word boundaries before and after match")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("before_ok")).to_equal(true)
expect(src.contains("after_ok")).to_equal(true)
```

</details>

#### uses pp_is_ident_char for boundary detection

- uses pp_is_ident_char for boundary detection
   - Expected: src contains `fn pp_is_ident_char`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses pp_is_ident_char for boundary detection")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("fn pp_is_ident_char")).to_equal(true)
```

</details>

### import_c defines — include processing

#### handles #include with file resolution

- handles #include with file resolution
   - Expected: src contains `directive == "include"`
   - Expected: src contains `fn pp_parse_include_path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles #include with file resolution")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("directive == \"include\"")).to_equal(true)
expect(src.contains("fn pp_parse_include_path")).to_equal(true)
```

</details>

#### recursively preprocesses included files

- recursively preprocesses included files
   - Expected: src contains `c_preprocess_with_include_root(inc_source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("recursively preprocesses included files")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("c_preprocess_with_include_root(inc_source")).to_equal(true)
```

</details>

#### reports error for missing includes

- reports error for missing includes
   - Expected: src contains `include not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports error for missing includes")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("include not found")).to_equal(true)
```

</details>

#### handles line continuation with backslash

- handles line continuation with backslash
   - Expected: src contains `ends_with("\\\\")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles line continuation with backslash")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("ends_with(\"\\\\\")")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/import_c_defines_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering import_c defines — system config forwarding, import_c defines — preprocessor conditionals, import_c defines — #define collection, import_c defines — macro expansion, import_c defines — include processing.
- import_c defines — system config forwarding
- import_c defines — preprocessor conditionals
- import_c defines — #define collection
- import_c defines — macro expansion
- import_c defines — include processing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `701466bc1c05551dc2656394594b62450d6f30d38eeb9c4bf50b87c860eee838`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `701466bc1c05551dc2656394594b62450d6f30d38eeb9c4bf50b87c860eee838`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `701466bc1c05551dc2656394594b62450d6f30d38eeb9c4bf50b87c860eee838`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/import_c_defines_spec.spl
mirror: doc/06_spec/03_system/compiler/import_c_defines_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/import_c_defines_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/import_c_defines_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/import_c_defines_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preprocessor accepts initial_defines parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/import_c_defines_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initial defines are copied into active define table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/import_c_defines_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CImportDefine carries name and value for forwarding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
