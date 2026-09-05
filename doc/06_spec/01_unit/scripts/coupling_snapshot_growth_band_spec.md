# Coupling Snapshot Growth Band Specification

> Tests covering coupling snapshot growth band.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coupling Snapshot Growth Band Specification

## Scenarios

### coupling snapshot growth band

#### POSITIVE CONTROL: growth beyond the +2% band FAILs (exit 1)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- POSITIVE CONTROL: growth beyond the +2% band FAILs (exit 1)
- Simulate 1000->1500 modules, 2000->3000 edges vs previous snapshot


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SCRIPTS
step("POSITIVE CONTROL: growth beyond the +2% band FAILs (exit 1)")
step("Simulate 1000->1500 modules, 2000->3000 edges vs previous snapshot")
val s = compare_fixture("modules 1500\\nedges 3000\\nlargest_scc 13\\n")
expect(s).to_contain("RC=1")
expect(s).to_contain("LAST=FAIL")
```

</details>

#### an in-band change PASSes (exit 0)

- an in-band change PASSes (exit 0)
- Simulate 1000->1010 modules, 2000->2020 edges — within the +2% band


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SCRIPTS
step("an in-band change PASSes (exit 0)")
step("Simulate 1000->1010 modules, 2000->2020 edges — within the +2% band")
val s = compare_fixture("modules 1010\\nedges 2020\\nlargest_scc 13\\n")
expect(s).to_contain("RC=0")
expect(s).to_contain("LAST=PASS")
```

</details>

#### largest-SCC growth alone FAILs even with modules/edges flat

- largest-SCC growth alone FAILs even with modules/edges flat
- Simulate largest_scc 13 -> 14 with no module/edge growth


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SCRIPTS
step("largest-SCC growth alone FAILs even with modules/edges flat")
step("Simulate largest_scc 13 -> 14 with no module/edge growth")
val s = compare_fixture("modules 1000\\nedges 2000\\nlargest_scc 14\\n")
expect(s).to_contain("RC=1")
expect(s).to_contain("LAST=FAIL")
```

</details>

#### the detector selftest itself is green (fatal fixtures incl. must-FAIL)

- the detector selftest itself is green (fatal fixtures incl. must-FAIL)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SCRIPTS
step("the detector selftest itself is green (fatal fixtures incl. must-FAIL)")
val out = process_run("sh", ["-c",
    "o=$(sh " + CHECK + " --selftest); rc=$?; last=$(printf '%s\\n' \"$o\" | tail -1); echo \"RC=$rc LAST=$last\""])
val s: text = out.0
expect(s).to_contain("RC=0")
expect(s).to_contain("LAST=PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/scripts/coupling_snapshot_growth_band_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering coupling snapshot growth band.
- coupling snapshot growth band

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

- `REQ-SSPEC-SCRIPTS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7ccfd5d3d9899b685f6b8a3a18794405a999a64ae5836666479206e39d1b1adc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7ccfd5d3d9899b685f6b8a3a18794405a999a64ae5836666479206e39d1b1adc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7ccfd5d3d9899b685f6b8a3a18794405a999a64ae5836666479206e39d1b1adc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/scripts/coupling_snapshot_growth_band_spec.spl
mirror: doc/06_spec/01_unit/scripts/coupling_snapshot_growth_band_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/scripts/coupling_snapshot_growth_band_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/scripts/coupling_snapshot_growth_band_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/scripts/coupling_snapshot_growth_band_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'POSITIVE CONTROL: growth beyond the +2% band FAILs (exit 1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/scripts/coupling_snapshot_growth_band_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an in-band change PASSes (exit 0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/scripts/coupling_snapshot_growth_band_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'largest-SCC growth alone FAILs even with modules/edges flat' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
