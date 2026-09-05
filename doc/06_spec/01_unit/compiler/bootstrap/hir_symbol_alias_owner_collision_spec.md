# Contract spec: test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl` and a green Results line.

## Scenarios

### HIR symbol owner remains unambiguous in the Stage3 closure

#### exports only the canonical HirSymbol declaration

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exports only the canonical HirSymbol declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports only the canonical HirSymbol declaration")
val types = file_read("src/compiler/20.hir/hir_types.spl")
val facade = file_read("src/compiler/20.hir/__init__.spl")

expect(types).to_contain("struct HirSymbol:")
expect(types).to_contain("symbols: Dict<i64, HirSymbol>")
expect(types).to_contain("export SymbolId, HirSymbol, SymbolKind, MethodResolution")
expect(types).to_not_contain("type Symbol = HirSymbol")        expect(types).to_not_contain("HirSymbol, Symbol, SymbolKind")        expect(facade).to_contain("SymbolId, HirSymbol, SymbolKind")
expect(facade).to_not_contain("SymbolId, Symbol, SymbolKind")
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


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the canonical type at explicit HIR consumer boundaries")
val visibility = file_read("src/compiler/35.semantics/visibility_checker.spl")
val interpreter = file_read("src/compiler/70.backend/backend/interpreter.spl")

expect(visibility).to_contain("symbol: HirSymbol")
expect(visibility).to_not_contain("symbol: Symbol")        expect(interpreter).to_contain("val sym: HirSymbol = sym_")
expect(interpreter).to_not_contain("val sym: Symbol = sym_")
```

</details>

#### does not register a struct Symbol that collides with the module-local type_alias Symbol

- does not register a struct Symbol that collides with the module-local type_alias Symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
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
expect(query_types).to_not_contain("struct Symbol:")        expect(compiler_query).to_contain("struct QuerySymbol:")
expect(compiler_query).to_not_contain("struct Symbol:")        expect(tools_init).to_contain("QuerySymbol, QuerySymbolV2")
expect(tools_init).to_not_contain(", Symbol, SymbolV2")
```

</details>

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

- Canonical SPipe generation for source `9b003e76f4a0b96ffa9d938c5b2216fe7ac7b747b9004e2bea55be98defaff6d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9b003e76f4a0b96ffa9d938c5b2216fe7ac7b747b9004e2bea55be98defaff6d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9b003e76f4a0b96ffa9d938c5b2216fe7ac7b747b9004e2bea55be98defaff6d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports only the canonical HirSymbol declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps unrelated module-local Symbol aliases intact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the canonical type at explicit HIR consumer boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
