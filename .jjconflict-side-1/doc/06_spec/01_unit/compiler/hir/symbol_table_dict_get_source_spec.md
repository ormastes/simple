# Symbol Table Dict Get Source Specification

> Tests covering SymbolTable Dict lookup source.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Symbol Table Dict Get Source Specification

## Scenarios

### SymbolTable Dict lookup source

#### uses the Dict runtime owner for scope symbol lookup

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the Dict runtime owner for scope symbol lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses the Dict runtime owner for scope symbol lookup")
val source = rt_file_read_text("src/compiler/20.hir/hir_types.spl") ?? ""

expect(source).to_contain("extern fn rt_dict_contains(dict: i64, key: Any) -> bool")
expect(source.contains("use std.alloc.sffi")).to_be(false)
expect(source).to_contain("if rt_dict_contains(scope.symbols, name):")
expect(source).to_contain("val found: i64 = scope.symbols[name]")
expect(source.contains("scope.symbols.get(name)")).to_be(false)
expect(source.contains("rt_dict_get(scope.symbols, name)")).to_be(false)
```

</details>

#### keeps display names in a symbol-id indexed text array

- keeps display names in a symbol-id indexed text array


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps display names in a symbol-id indexed text array")
val source = rt_file_read_text("src/compiler/20.hir/hir_types.spl") ?? ""

expect(source).to_contain("display_names: [text]")
expect(source).to_contain("self.display_names = self.display_names.push(name)")
expect(source).to_contain("return self.display_names[raw]")
expect(source).to_contain("self.display_names[raw] = new_name")
```

</details>

#### lowers identifiers through a validated nonoptional symbol id

- lowers identifiers through a validated nonoptional symbol id
   - Expected: source does not contain `if val found_symbol = symbol:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers identifiers through a validated nonoptional symbol id")
val source = rt_file_read_text("src/compiler/20.hir/hir_lowering/expressions.spl") ?? ""

expect(source).to_contain("val found_symbol = self.symbols.lookup_or_invalid(ident_name_t)")
expect(source).to_contain("if found_symbol.is_valid():")
expect(source.contains("if val found_symbol = symbol:")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/symbol_table_dict_get_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SymbolTable Dict lookup source.
- SymbolTable Dict lookup source

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `678a7c30adabddb4be654251d5e443317d9b72c8b5c75fec4905b98bd49f7e71`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `678a7c30adabddb4be654251d5e443317d9b72c8b5c75fec4905b98bd49f7e71`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `678a7c30adabddb4be654251d5e443317d9b72c8b5c75fec4905b98bd49f7e71`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/hir/symbol_table_dict_get_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/symbol_table_dict_get_source_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/hir/symbol_table_dict_get_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/symbol_table_dict_get_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/symbol_table_dict_get_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/hir/symbol_table_dict_get_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/hir/symbol_table_dict_get_source_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the Dict runtime owner for scope symbol lookup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/symbol_table_dict_get_source_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps display names in a symbol-id indexed text array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/symbol_table_dict_get_source_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers identifiers through a validated nonoptional symbol id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
