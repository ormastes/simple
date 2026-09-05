# hwir_zca_target_trap_exhaustive_oracle_spec

> Exhaustively execute the composed strict HWIR graph for every 16-bit parcel.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hwir_zca_target_trap_exhaustive_oracle_spec

Exhaustively execute the composed strict HWIR graph for every 16-bit parcel.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_zca_target_trap_exhaustive_oracle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exhaustively execute the composed strict HWIR graph for every 16-bit parcel.

This test deliberately has no parallel decoder/classifier.  Its oracle is the
typed target-trap graph itself, executed through two separately prepared
evaluators.  The assertions validate the closed output partition and exact
tuple determinism for both concrete critical products.

## Scenarios

### RISC-V Gen2 exhaustive target-trap parcel oracle

#### should exhaustively execute every RV32 and RV64 parcel through two prepared strict graphs

- should exhaustively execute every RV32 and RV64 parcel through two prepared strict graphs
- Sweep the complete 16-bit parcel space without an independent decoder proxy
   - Expected: counts[0] + counts[1] equals `65536`
   - Expected: counts[2] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should exhaustively execute every RV32 and RV64 parcel through two prepared strict graphs")
step("Sweep the complete 16-bit parcel space without an independent decoder proxy")
for config in [CoreConfig.rv32_zca_cjal_mission_critical(),
    CoreConfig.rv64_zca_addiw_mission_critical()]:
    val counts = run_target_trap_parcel_oracle(config, 65536)
    expect(counts[0] + counts[1]).to_equal(65536)
    expect(counts[0]).to_be_greater_than(0)
    expect(counts[1]).to_be_greater_than(0)
    expect(counts[2]).to_equal(1)
```

</details>

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

- `REQ-SSPEC-UNIT`
- `REQ-G2-002`
- `REQ-G2-010`
- `REQ-G2-011`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `94da17ed20a53c2d271f345f7de4c4848cc60b967e05bbecef42853a590a1dcc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `94da17ed20a53c2d271f345f7de4c4848cc60b967e05bbecef42853a590a1dcc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `94da17ed20a53c2d271f345f7de4c4848cc60b967e05bbecef42853a590a1dcc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/50.mir/hwir_zca_target_trap_exhaustive_oracle_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_zca_target_trap_exhaustive_oracle_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=95 oracle=80
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/50.mir/hwir_zca_target_trap_exhaustive_oracle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_zca_target_trap_exhaustive_oracle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_zca_target_trap_exhaustive_oracle_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_zca_target_trap_exhaustive_oracle_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/50.mir/hwir_zca_target_trap_exhaustive_oracle_spec.spl:136:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should exhaustively execute every RV32 and RV64 parcel through two prepared strict graphs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_zca_target_trap_exhaustive_oracle_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should exhaustively execute every RV32 and RV64 parcel through two prepared strict graphs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
