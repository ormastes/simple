# Hir Module Callable Index Specification

> Tests covering HIR module-callable index.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Module Callable Index Specification

## Scenarios

### HIR module-callable index

#### never materializes the whole symbol table per lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
# @req REQ-SSPEC-UNIT
# `self.symbols.symbols.keys()` was the sweep, and this file is the
# only place it ever appeared. Its absence, together with the index
# call that replaced it, is the mechanism assertion.
val source = expression_support_source()
expect(source.contains("me field_module_callable(module_name: text, field_name: text) -> SymbolId?:")).to_equal(true)
expect(source.contains("val candidate_keys = self.symbols.symbols.keys()")).to_equal(false)
expect(source.contains("self.symbols.module_callable_raw(module_name, field_name)")).to_equal(true)
```

</details>

#### answers an exact cross-module name in O(1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SymbolTable.new()
val id = table.define("answer", SymbolKind.Function, nil, Span.empty(),
    Visibility.Public, false, Some("pkg.provider"))
expect(table.module_callable_raw("pkg.provider", "answer")).to_equal(id.id)
```

</details>

#### answers a dotted name by its last segment, as the sweep did

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SymbolTable.new()
val id = table.define("pkg.provider.answer", SymbolKind.Function, nil,
    Span.empty(), Visibility.Public, false, Some("pkg.provider"))
expect(table.module_callable_raw("pkg.provider", "answer")).to_equal(id.id)
```

</details>

#### lets the latest registration win, as the reverse scan did

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SymbolTable.new()
val _first = table.define("answer", SymbolKind.Function, nil, Span.empty(),
    Visibility.Public, false, Some("pkg.provider"))
val second = table.define("answer", SymbolKind.Function, nil, Span.empty(),
    Visibility.Public, false, Some("pkg.provider"))
expect(table.module_callable_raw("pkg.provider", "answer")).to_equal(second.id)
```

</details>

#### does not answer for a different defining module

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SymbolTable.new()
val _id = table.define("answer", SymbolKind.Function, nil, Span.empty(),
    Visibility.Public, false, Some("pkg.provider"))
expect(table.module_callable_raw("pkg.other", "answer")).to_equal(-1)
```

</details>

#### indexes nothing for a module-less local symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SymbolTable.new()
val _id = table.define("local_only", SymbolKind.Variable, nil, Span.empty(),
    Visibility.Private, true, nil)
expect(table.module_callables.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_module_callable_index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HIR module-callable index.
- HIR module-callable index

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `0f65b61fa6c7d681b171cba8bda59045c06f500f07f9431ac06bf5ce5ba8fb5e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0f65b61fa6c7d681b171cba8bda59045c06f500f07f9431ac06bf5ce5ba8fb5e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0f65b61fa6c7d681b171cba8bda59045c06f500f07f9431ac06bf5ce5ba8fb5e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **75/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/hir/hir_module_callable_index_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_module_callable_index_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=60 oracle=30
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=75; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/hir/hir_module_callable_index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_module_callable_index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_module_callable_index_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/hir/hir_module_callable_index_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/hir/hir_module_callable_index_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/hir_module_callable_index_spec.spl:38:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'never materializes the whole symbol table per lookup' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/hir/hir_module_callable_index_spec.spl:50:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'answers an exact cross-module name in O(1)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/hir/hir_module_callable_index_spec.spl:57:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'answers a dotted name by its last segment, as the sweep did' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/hir/hir_module_callable_index_spec.spl:64:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'lets the latest registration win, as the reverse scan did' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
