# Hir Symbol Table Shared Binding Contract Specification

> Tests covering HIR symbol table strict shared bindings.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Symbol Table Shared Binding Contract Specification

## Scenarios

### HIR symbol table strict shared bindings

#### returns raw symbol lookups without a mutable optional accumulator

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns raw symbol lookups without a mutable optional accumulator
   - Expected: hit.?.name equals `compute_a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns raw symbol lookups without a mutable optional accumulator")
val table = SymbolTable.new()
table.register_preserved_symbol(probe_symbol(7, "compute_a", Some("m.alpha")))
# oracle: registered raw id must come back with the exact name
val hit = table.get_symbol_raw(7)
assert_true(hit != nil)
expect(hit.?.name).to_equal("compute_a")
# oracle: an absent raw id must answer nil, not a stale accumulator value
assert_nil(table.get_symbol_raw(999))
```

</details>

#### renames a symbol in place without disturbing the raw id mapping

- rename_symbol overwrites the stored name for the same raw id
   - Expected: table.get_symbol_raw(11).?.name equals `m.beta.helper_fn`
   - Expected: table.symbol_display_name(SymbolId(id: 11), "fallback") equals `m.beta.helper_fn`
   - Expected: table.symbol_display_name(SymbolId(id: 404), "fallback") equals `fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rename_symbol overwrites the stored name for the same raw id")
val table = SymbolTable.new()
table.register_preserved_symbol(probe_symbol(11, "helper_fn", Some("m.beta")))
table.rename_symbol(SymbolId(id: 11), "m.beta.helper_fn")
# oracle: same id resolves to the renamed entry after an immutable rebuild
expect(table.get_symbol_raw(11).?.name).to_equal("m.beta.helper_fn")
expect(table.symbol_display_name(SymbolId(id: 11), "fallback")).to_equal("m.beta.helper_fn")
# oracle: display name falls back only for an unknown id
expect(table.symbol_display_name(SymbolId(id: 404), "fallback")).to_equal("fallback")
```

</details>

#### indexes module callables for defining-module lookups in O(1)

- register_preserved_symbol answers module_callable_raw without a table sweep
   - Expected: table.module_callable_raw("m.gamma", "dotted.field_fn") equals `21`
   - Expected: table.module_callable_raw("m.gamma", "field_fn") equals `21`
   - Expected: table.module_callable_raw("m.gamma", "absent_fn") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("register_preserved_symbol answers module_callable_raw without a table sweep")
val table = SymbolTable.new()
table.register_preserved_symbol(probe_symbol(21, "dotted.field_fn", Some("m.gamma")))
# oracle: both full name and last dotted segment are indexed to the raw id
expect(table.module_callable_raw("m.gamma", "dotted.field_fn")).to_equal(21)
expect(table.module_callable_raw("m.gamma", "field_fn")).to_equal(21)
# oracle: an unindexed (module, field) pair answers -1
# oracle: -1 is the documented miss sentinel, not 0 and not nil
expect(table.module_callable_raw("m.gamma", "absent_fn")).to_equal(-1)
# oracle: exact-name type lookup misses for a Function-kind symbol
assert_nil(table.lookup_exact_type("dotted.field_fn"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/hir_symbol_table_shared_binding_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HIR symbol table strict shared bindings.
- HIR symbol table strict shared bindings

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `473aeb6f42b8b5bb19ba9946d0fb2d2ce64bd8da154f576353b871468e3234cf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `473aeb6f42b8b5bb19ba9946d0fb2d2ce64bd8da154f576353b871468e3234cf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `473aeb6f42b8b5bb19ba9946d0fb2d2ce64bd8da154f576353b871468e3234cf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/bootstrap/hir_symbol_table_shared_binding_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/hir_symbol_table_shared_binding_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bootstrap/hir_symbol_table_shared_binding_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/hir_symbol_table_shared_binding_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/hir_symbol_table_shared_binding_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/bootstrap/hir_symbol_table_shared_binding_contract_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns raw symbol lookups without a mutable optional accumulator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/hir_symbol_table_shared_binding_contract_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renames a symbol in place without disturbing the raw id mapping' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/hir_symbol_table_shared_binding_contract_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'indexes module callables for defining-module lookups in O(1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
