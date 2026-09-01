# Symbol Table Qualified Indexes Specification

> Tests covering SymbolTable qualified and exact indexes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Symbol Table Qualified Indexes Specification

## Scenarios

### SymbolTable qualified and exact indexes

#### constructs all indexes and preserves qualified function id zero

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- constructs all indexes and preserves qualified function id zero
   - Expected: symbols.lookup_qualified_function_raw("owner", "first") equals `0`
   - Expected: symbols.lookup_qualified_function_raw("owner", "missing") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("constructs all indexes and preserves qualified function id zero")
var symbols = SymbolTable.new()
symbols.bind_qualified_function("owner", "first", SymbolId(id: 0))
symbols.bind_qualified_function("owner", "first", SymbolId(id: 7))

expect(symbols.lookup_qualified_function_raw("owner", "first")).to_equal(0)
expect(symbols.lookup_qualified_function_raw("owner", "missing")).to_equal(-1)
match symbols.lookup_qualified_function("owner", "first"):
    case Some(found): expect(found.id).to_equal(0)
    case nil: expect(false).to_equal(true)
```

</details>

#### preserves qualified type first-write and missing sentinels

- preserves qualified type first-write and missing sentinels
   - Expected: symbols.lookup_qualified_type_raw("owner", "Item") equals `0`
   - Expected: symbols.lookup_qualified_type_raw("other", "Item") equals `9`
   - Expected: symbols.lookup_qualified_type_raw("owner", "Other") equals `10`
   - Expected: symbols.lookup_qualified_type_raw("owner", "Missing") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves qualified type first-write and missing sentinels")
var symbols = SymbolTable.new()
symbols.bind_qualified_type("owner", "Item", SymbolId(id: 0))
symbols.bind_qualified_type("owner", "Item", SymbolId(id: 8))
symbols.bind_qualified_type("other", "Item", SymbolId(id: 9))
symbols.bind_qualified_type("owner", "Other", SymbolId(id: 10))

expect(symbols.lookup_qualified_type_raw("owner", "Item")).to_equal(0)
expect(symbols.lookup_qualified_type_raw("other", "Item")).to_equal(9)
expect(symbols.lookup_qualified_type_raw("owner", "Other")).to_equal(10)
expect(symbols.lookup_qualified_type_raw("owner", "Missing")).to_equal(-1)
```

</details>

#### resets scalar qualified indexes with module state

- resets scalar qualified indexes with module state
   - Expected: symbols.lookup_qualified_type_raw("owner", "Item") equals `-1`
   - Expected: symbols.lookup_qualified_function_raw("owner", "call") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resets scalar qualified indexes with module state")
var symbols = SymbolTable.new()
symbols.bind_qualified_type("owner", "Item", SymbolId(id: 4))
symbols.bind_qualified_function("owner", "call", SymbolId(id: 5))
symbols.reset_module()
expect(symbols.lookup_qualified_type_raw("owner", "Item")).to_equal(-1)
expect(symbols.lookup_qualified_function_raw("owner", "call")).to_equal(-1)
```

</details>

#### indexes exact definitions and keeps old aliases after rename

- indexes exact definitions and keeps old aliases after rename


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("indexes exact definitions and keeps old aliases after rename")
var symbols = SymbolTable.new()
val id = symbols.define(
    "Alias",
    SymbolKind.Struct,
    nil,
    Span.empty(),
    Visibility.Private,
    false,
    nil
)
symbols.rename_symbol(id, "owner.Item")

match symbols.lookup_exact_type("Alias"):
    case Some(found): expect(found.id).to_equal(id.id)
    case nil: expect(false).to_equal(true)
match symbols.lookup_exact_type("owner.Item"):
    case Some(found): expect(found.id).to_equal(id.id)
    case nil: expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/symbol_table_qualified_indexes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SymbolTable qualified and exact indexes.
- SymbolTable qualified and exact indexes

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7a408402d2a6e74fbd38f1b63107f93313a1f62794cabeef2c4e5bd42096c7f8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7a408402d2a6e74fbd38f1b63107f93313a1f62794cabeef2c4e5bd42096c7f8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7a408402d2a6e74fbd38f1b63107f93313a1f62794cabeef2c4e5bd42096c7f8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/hir/symbol_table_qualified_indexes_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/symbol_table_qualified_indexes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/symbol_table_qualified_indexes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/symbol_table_qualified_indexes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/symbol_table_qualified_indexes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/symbol_table_qualified_indexes_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs all indexes and preserves qualified function id zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/symbol_table_qualified_indexes_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves qualified type first-write and missing sentinels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/symbol_table_qualified_indexes_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resets scalar qualified indexes with module state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
