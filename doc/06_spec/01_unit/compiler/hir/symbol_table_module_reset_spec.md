# Symbol Table Module Reset Specification

> Tests covering SymbolTable module reset owns fresh name and id state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Symbol Table Module Reset Specification

## Scenarios

### SymbolTable module reset owns fresh name and id state

#### drops prior-module names before reusing symbol ids

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- drops prior-module names before reusing symbol ids
   - Expected: old_id.id equals `0`
   - Expected: new_id.id equals `0`
   - Expected: symbols.lookup_or_invalid("NewModuleValue").id equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("drops prior-module names before reusing symbol ids")
var symbols = SymbolTable.new()
val old_id = symbols.define(
    "OldModuleType", SymbolKind.Struct, nil, Span.empty(),
    Visibility.Private, false, nil)
expect(old_id.id).to_equal(0)

symbols.reset_module()

val new_id = symbols.define(
    "NewModuleValue", SymbolKind.Variable, nil, Span.empty(),
    Visibility.Private, false, nil)
expect(new_id.id).to_equal(0)
expect(symbols.lookup_or_invalid("OldModuleType").is_valid()).to_be(false)
expect(symbols.lookup_or_invalid("NewModuleValue").id).to_equal(0)
```

</details>

#### fails closed when a stale name points outside the live id interval

- fails closed when a stale name points outside the live id interval
   - Expected: found.id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails closed when a stale name points outside the live id interval")
var symbols = SymbolTable.new()
symbols.root_scope_symbols["Stale"] = 41
var root = symbols.scopes[0]
root.symbols["Stale"] = 41
symbols.scopes[0] = root

val found = symbols.lookup_or_invalid("Stale")
expect(found.is_valid()).to_be(false)
expect(found.id).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/symbol_table_module_reset_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SymbolTable module reset owns fresh name and id state.
- SymbolTable module reset owns fresh name and id state

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `f7709409bfb94702bb375b9eb08a1e6ded736909ea44b2518bfe1c0fa8d532d7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f7709409bfb94702bb375b9eb08a1e6ded736909ea44b2518bfe1c0fa8d532d7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f7709409bfb94702bb375b9eb08a1e6ded736909ea44b2518bfe1c0fa8d532d7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/hir/symbol_table_module_reset_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/symbol_table_module_reset_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/symbol_table_module_reset_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/symbol_table_module_reset_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/symbol_table_module_reset_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/symbol_table_module_reset_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'drops prior-module names before reusing symbol ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/symbol_table_module_reset_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when a stale name points outside the live id interval' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
