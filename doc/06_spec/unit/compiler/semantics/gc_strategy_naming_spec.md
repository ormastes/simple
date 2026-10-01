# gc_strategy_naming_spec

> GC mode and barrier strategy naming regression.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gc_strategy_naming_spec

GC mode and barrier strategy naming regression.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/semantics/gc_strategy_naming_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

GC mode and barrier strategy naming regression.

Family-level GC mode and MIR barrier strategy are separate concepts; this keeps
their type names separate so imports stay unambiguous.

## Scenarios

### GC strategy naming

#### has only one compiler enum named GcMode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has only one compiler enum named GcMode
   - Expected: matches.len() equals `1`
   - Expected: matches[0].starts_with("src/compiler/00.common/gc_config.spl:") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has only one compiler enum named GcMode")
val matches = _non_empty_scan_lines(_scan("enum GcMode:", "src/compiler"))
expect(matches.len()).to_equal(1)
expect(matches[0].starts_with("src/compiler/00.common/gc_config.spl:")).to_equal(true)
```

</details>

#### uses GcStrategy for write barrier GC algorithms

- uses GcStrategy for write barrier GC algorithms
   - Expected: matches.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses GcStrategy for write barrier GC algorithms")
val matches = _non_empty_scan_lines(_scan("enum GcStrategy:", "src/compiler/55.borrow/gc_analysis/barriers.spl"))
expect(matches.len()).to_equal(1)
```

</details>

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `df337dd7e67c2322eed5cf2de85d6c5fca09412eee6053bba4582653a288b85f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `df337dd7e67c2322eed5cf2de85d6c5fca09412eee6053bba4582653a288b85f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `df337dd7e67c2322eed5cf2de85d6c5fca09412eee6053bba4582653a288b85f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/semantics/gc_strategy_naming_spec.spl
mirror: doc/06_spec/unit/compiler/semantics/gc_strategy_naming_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/semantics/gc_strategy_naming_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/semantics/gc_strategy_naming_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/semantics/gc_strategy_naming_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/semantics/gc_strategy_naming_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has only one compiler enum named GcMode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/gc_strategy_naming_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses GcStrategy for write barrier GC algorithms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
