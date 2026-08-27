# parser_category_c_spec

> Regression coverage for compiled_checker_parser_category_c_2026_08_03.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# parser_category_c_spec

Regression coverage for compiled_checker_parser_category_c_2026_08_03.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/parser_category_c_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression coverage for compiled_checker_parser_category_c_2026_08_03.

Declaration/import/export parsing accepts canonical contextual identifiers,
while malformed input still diagnoses and a following valid parse recovers.

## Scenarios

### compiled checker parser category C

#### parses the exact keyword-named free function family

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses the exact keyword-named free function family
   - Expected: parses_clean("category_c_keyword_functions.spl", keyword_function_source()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the exact keyword-named free function family")
expect(parses_clean("category_c_keyword_functions.spl", keyword_function_source())).to_equal(true)
```

</details>

#### keeps ordinary and extern function names adjacent to keyword names

- keeps ordinary and extern function names adjacent to keyword names
   - Expected: parses_clean("category_c_adjacent_functions.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps ordinary and extern function names adjacent to keyword names")
val source = "fn ordinary() -> i64: 1\n" +
    "extern fn new() -> i64\n"
expect(parses_clean("category_c_adjacent_functions.spl", source)).to_equal(true)
```

</details>

#### reports a malformed function name then recovers for valid keyword names

- reports a malformed function name then recovers for valid keyword names
   - Expected: parses_clean("category_c_bad_function.spl", "fn () -> i64: 1\n") is false
   - Expected: parses_clean("category_c_function_recovery.spl", keyword_function_source()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a malformed function name then recovers for valid keyword names")
expect(parses_clean("category_c_bad_function.spl", "fn () -> i64: 1\n")).to_equal(false)
expect(parses_clean("category_c_function_recovery.spl", keyword_function_source())).to_equal(true)
```

</details>

#### parses exact bare glob structured and empty export forms

- parses exact bare glob structured and empty export forms
   - Expected: parses_clean("category_c_exports.spl", export_source()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses exact bare glob structured and empty export forms")
expect(parses_clean("category_c_exports.spl", export_source())).to_equal(true)
```

</details>

#### parses adjacent keyword aliases and dotted export sources

- parses adjacent keyword aliases and dotted export sources
   - Expected: parses_clean("category_c_adjacent_exports.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses adjacent keyword aliases and dotted export sources")
val source = "export {new as fresh, lazy} from nested.module\n" +
    "export ordinary\n"
expect(parses_clean("category_c_adjacent_exports.spl", source)).to_equal(true)
```

</details>

#### reports a malformed structured export then recovers for valid exports

- reports a malformed structured export then recovers for valid exports
   - Expected: parses_clean("category_c_bad_export.spl", "export {new lazy} from config\n") is false
   - Expected: parses_clean("category_c_export_recovery.spl", export_source()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a malformed structured export then recovers for valid exports")
expect(parses_clean("category_c_bad_export.spl", "export {new lazy} from config\n")).to_equal(false)
expect(parses_clean("category_c_export_recovery.spl", export_source())).to_equal(true)
```

</details>

#### parses the exact triple-dot import and adjacent relative depths

- parses the exact triple-dot import and adjacent relative depths
   - Expected: parses_clean("category_c_relative_imports.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the exact triple-dot import and adjacent relative depths")
val source = "use ...monomorphize.note_sdn (NoteSdnMetadata, InstantiationEntry)\n" +
    "use ..linker.smf_reader\n" +
    "use .sibling\n" +
    "fn load_header() -> i64:\n" +
    "    use ..linker.smf_enums (Platform, Arch)\n" +
    "    1\n"
expect(parses_clean("category_c_relative_imports.spl", source)).to_equal(true)
```

</details>

#### reports a malformed relative path then recovers for the exact import

- reports a malformed relative path then recovers for the exact import
   - Expected: parses_clean("category_c_bad_relative.spl", "use ...monomorphize.42\n") is false
   - Expected: parses_clean("category_c_relative_recovery.spl", "use ...monomorphize.note_sdn\n") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a malformed relative path then recovers for the exact import")
expect(parses_clean("category_c_bad_relative.spl", "use ...monomorphize.42\n")).to_equal(false)
expect(parses_clean("category_c_relative_recovery.spl", "use ...monomorphize.note_sdn\n")).to_equal(true)
```

</details>

#### parses the remaining keyword class method and mutable receiver family

- parses the remaining keyword class method and mutable receiver family
   - Expected: parses_clean("category_c_class_keywords.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the remaining keyword class method and mutable receiver family")
val source = "class KeywordMethods:\n" +
    "    static fn nil() -> i64: 0\n" +
    "    static fn match() -> i64: 1\n" +
    "    me fn after() -> i64: 2\n"
expect(parses_clean("category_c_class_keywords.spl", source)).to_equal(true)
```

</details>

#### keeps keyword receivers generic calls and underscore comprehensions adjacent

- keeps keyword receivers generic calls and underscore comprehensions adjacent
   - Expected: parses_clean("category_c_primary_surfaces.spl", source) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps keyword receivers generic calls and underscore comprehensions adjacent")
val source = "fn surfaces(items: [i64]) -> i64:\n" +
    "    val lazy = items\n" +
    "    val count = lazy.len()\n" +
    "    val mapped = [for _ in items: count]\n" +
    "    count\n"
expect(parses_clean("category_c_primary_surfaces.spl", source)).to_equal(true)
```

</details>

#### parses tuple and while-val patterns without weakening malformed patterns

- parses tuple and while-val patterns without weakening malformed patterns
   - Expected: parses_clean("category_c_patterns.spl", source) is true
   - Expected: parses_clean("category_c_bad_tuple_pattern.spl", "fn bad():\n    val (left,) =\n") is false
   - Expected: parses_clean("category_c_pattern_recovery.spl", "fn good(): i64: 1\n") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses tuple and while-val patterns without weakening malformed patterns")
val source = "fn patterns(value: Option<i64>) -> i64:\n" +
    "    val (left, right) = (1, 2)\n" +
    "    while val Some(item) = value:\n" +
    "        return left + right + item\n" +
    "    0\n"
expect(parses_clean("category_c_patterns.spl", source)).to_equal(true)
expect(parses_clean("category_c_bad_tuple_pattern.spl", "fn bad():\n    val (left,) =\n")).to_equal(false)
expect(parses_clean("category_c_pattern_recovery.spl", "fn good(): i64: 1\n")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `f65f9e36d62b4455e126fa568d30202c415d2fa4a56aefc932b796c38b919221`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f65f9e36d62b4455e126fa568d30202c415d2fa4a56aefc932b796c38b919221`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f65f9e36d62b4455e126fa568d30202c415d2fa4a56aefc932b796c38b919221`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser/parser_category_c_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/parser_category_c_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/parser_category_c_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/parser_category_c_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/parser_category_c_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the exact keyword-named free function family' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/parser_category_c_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps ordinary and extern function names adjacent to keyword names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/parser_category_c_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a malformed function name then recovers for valid keyword names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
