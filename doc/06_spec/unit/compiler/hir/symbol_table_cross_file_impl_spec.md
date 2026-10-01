# Symbol Table Cross File Impl Specification

> Tests covering SymbolTable methods across two impl blocks in two files.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Symbol Table Cross File Impl Specification

## Scenarios

### SymbolTable methods across two impl blocks in two files

#### reaches the second block through a direct module import

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reaches the second block through a direct module import
   - Expected: t.lookup_or_invalid("absent").id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reaches the second block through a direct module import")
var t = SymbolTable.new()
expect(t.lookup_or_invalid("absent").id).to_equal(-1)
```

</details>

#### reaches the second block through the package facade

- reaches the second block through the package facade
   - Expected: t.lookup_or_invalid("absent").id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reaches the second block through the package facade")
var t = FacadeSymbolTable.new()
expect(t.lookup_or_invalid("absent").id).to_equal(-1)
```

</details>

#### reaches the second block on a transitively owned SymbolTable

- reaches the second block on a transitively owned SymbolTable
   - Expected: lowering.symbols.lookup_or_invalid("absent").id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reaches the second block on a transitively owned SymbolTable")
var lowering = HirLowering.new()
expect(lowering.symbols.lookup_or_invalid("absent").id).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/hir/symbol_table_cross_file_impl_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SymbolTable methods across two impl blocks in two files.
- SymbolTable methods across two impl blocks in two files

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f500b9123850a5f5c9f2c655d098ca89f23919d487008108779c6cb207cae1d8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f500b9123850a5f5c9f2c655d098ca89f23919d487008108779c6cb207cae1d8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f500b9123850a5f5c9f2c655d098ca89f23919d487008108779c6cb207cae1d8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/hir/symbol_table_cross_file_impl_spec.spl
mirror: doc/06_spec/unit/compiler/hir/symbol_table_cross_file_impl_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/hir/symbol_table_cross_file_impl_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/hir/symbol_table_cross_file_impl_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/hir/symbol_table_cross_file_impl_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/hir/symbol_table_cross_file_impl_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reaches the second block through a direct module import' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/hir/symbol_table_cross_file_impl_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reaches the second block through the package facade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/hir/symbol_table_cross_file_impl_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reaches the second block on a transitively owned SymbolTable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
