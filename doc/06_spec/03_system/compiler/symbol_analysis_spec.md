# Symbol Analysis Specification

> Tests covering Symbol Analysis.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Symbol Analysis Specification

## Scenarios

### Symbol Analysis

#### marks entry-point references reachable and reports dead symbols

- marks entry-point references reachable and reports dead symbols
   - Expected: stats.total_symbols equals `3`
   - Expected: stats.reachable_symbols equals `2`
   - Expected: stats.dead_symbols equals `1`
   - Expected: stats.dead_size equals `16`
   - Expected: stats.total_size equals `112`
   - Expected: removable.len() equals `1`
   - Expected: removable[0] equals `unused`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("marks entry-point references reachable and reports dead symbols")
"""Entry points and call references should keep only connected symbols live."""
var analyzer = SymbolAnalyzer.create()
analyzer.add_symbol("main", SymbolVisibility.Export, 64, ".text")
analyzer.add_symbol("helper", SymbolVisibility.Local, 32, ".text")
analyzer.add_symbol("unused", SymbolVisibility.Local, 16, ".text")
analyzer.add_reference("main", "helper", RefKind.Call)
analyzer.set_entry_point("main")

_ = analyzer.analyze()

val stats = analyzer.stats()
expect(stats.total_symbols).to_equal(3)
expect(stats.reachable_symbols).to_equal(2)
expect(stats.dead_symbols).to_equal(1)
expect(stats.dead_size).to_equal(16)
expect(stats.total_size).to_equal(112)

val removable = analyzer.get_removable_symbols()
expect(removable.len()).to_equal(1)
expect(removable[0]).to_equal("unused")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/symbol_analysis_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Symbol Analysis.
- Symbol Analysis

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `fdeb8df7895e5bdb7fe5ed325cac6fcc0b4593ee44a3225f4a4fc6b8cdbf9141`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fdeb8df7895e5bdb7fe5ed325cac6fcc0b4593ee44a3225f4a4fc6b8cdbf9141`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fdeb8df7895e5bdb7fe5ed325cac6fcc0b4593ee44a3225f4a4fc6b8cdbf9141`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/compiler/symbol_analysis_spec.spl
mirror: doc/06_spec/03_system/compiler/symbol_analysis_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/symbol_analysis_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/symbol_analysis_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/symbol_analysis_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/symbol_analysis_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks entry-point references reachable and reports dead symbols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
