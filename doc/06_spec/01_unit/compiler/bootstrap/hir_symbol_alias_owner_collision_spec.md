# Hir Symbol Alias Owner Collision Specification

> Tests covering HIR symbol owner remains unambiguous in the Stage3 closure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Symbol Alias Owner Collision Specification

## Scenarios

### HIR symbol owner remains unambiguous in the Stage3 closure

#### exports only the canonical HirSymbol declaration

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exports only the canonical HirSymbol declaration
   - Expected: types does not contain `type Symbol = HirSymbol`
   - Expected: types does not contain `HirSymbol, Symbol, SymbolKind`
   - Expected: facade does not contain `SymbolId, Symbol, SymbolKind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports only the canonical HirSymbol declaration")
val types = file_read("src/compiler/20.hir/hir_types.spl")
val facade = file_read("src/compiler/20.hir/__init__.spl")

expect(types).to_contain("struct HirSymbol:")
expect(types).to_contain("symbols: Dict<i64, HirSymbol>")
expect(types).to_contain("export SymbolId, HirSymbol, SymbolKind, MethodResolution")
expect(types.contains("type Symbol = HirSymbol")).to_equal(false)
expect(types.contains("HirSymbol, Symbol, SymbolKind")).to_equal(false)
expect(facade).to_contain("SymbolId, HirSymbol, SymbolKind")
expect(facade.contains("SymbolId, Symbol, SymbolKind")).to_equal(false)
```

</details>

#### keeps unrelated module-local Symbol aliases intact

- keeps unrelated module-local Symbol aliases intact


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps unrelated module-local Symbol aliases intact")
val associated_types = file_read("src/compiler/30.types/associated_types_defs.spl")
expect(associated_types).to_contain("type Symbol = text")
expect(associated_types).to_contain("export Symbol")
```

</details>

#### uses the canonical type at explicit HIR consumer boundaries

- uses the canonical type at explicit HIR consumer boundaries
   - Expected: visibility does not contain `symbol: Symbol`
   - Expected: interpreter does not contain `val sym: Symbol = sym_`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the canonical type at explicit HIR consumer boundaries")
val visibility = file_read("src/compiler/35.semantics/visibility_checker.spl")
val interpreter = file_read("src/compiler/70.backend/backend/interpreter.spl")

expect(visibility).to_contain("symbol: HirSymbol")
expect(visibility.contains("symbol: Symbol")).to_equal(false)
expect(interpreter).to_contain("val sym: HirSymbol = sym_")
expect(interpreter.contains("val sym: Symbol = sym_")).to_equal(false)
```

</details>

#### does not register a struct Symbol that collides with the module-local type_alias Symbol

- does not register a struct Symbol that collides with the module-local type_alias Symbol
   - Expected: query_types does not contain `struct Symbol:`
   - Expected: compiler_query does not contain `struct Symbol:`
   - Expected: tools_init does not contain `, Symbol, SymbolV2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not register a struct Symbol that collides with the module-local type_alias Symbol")
# Regression for doc/08_tracking/bug/stage3_selfhost_symbol_alias_conflict_2026-08-04.md
# part A: driver_source_loading.spl's Stage-3 closure pulls in both
# `struct Symbol` (query_types.spl / compiler_query.spl, under
# 90.tools) and `type Symbol = text` (00.common/effects.spl,
# 30.types/*.spl). Same-named global type registry entries of
# different kinds (struct vs type_alias) fail HIR lowering with
# "enum payload dependency `Symbol` conflicts: ...struct vs
# ...type_alias". Fix: rename the query-tool structs to
# QuerySymbol/QuerySymbolV2 so no `struct Symbol` remains anywhere.
val query_types = file_read("src/compiler/90.tools/query_types.spl")
val compiler_query = file_read("src/compiler/90.tools/sffi_gen/specs/compiler_query.spl")
val tools_init = file_read("src/compiler/90.tools/__init__.spl")

expect(query_types).to_contain("struct QuerySymbol:")
expect(query_types.contains("struct Symbol:")).to_equal(false)
expect(compiler_query).to_contain("struct QuerySymbol:")
expect(compiler_query.contains("struct Symbol:")).to_equal(false)
expect(tools_init).to_contain("QuerySymbol, QuerySymbolV2")
expect(tools_init.contains(", Symbol, SymbolV2")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HIR symbol owner remains unambiguous in the Stage3 closure.
- HIR symbol owner remains unambiguous in the Stage3 closure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `3ec77bb49643b49c14d95d9f9880fb440c7788d8ef039a60ba3b80bc76b07c57`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3ec77bb49643b49c14d95d9f9880fb440c7788d8ef039a60ba3b80bc76b07c57`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3ec77bb49643b49c14d95d9f9880fb440c7788d8ef039a60ba3b80bc76b07c57`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports only the canonical HirSymbol declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps unrelated module-local Symbol aliases intact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the canonical type at explicit HIR consumer boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
