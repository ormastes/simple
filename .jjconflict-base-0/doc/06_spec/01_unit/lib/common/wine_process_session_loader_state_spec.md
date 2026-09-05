# Wine Process Session Loader State Specification

> Tests covering Wine process session import loader state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Loader State Specification

## Scenarios

### Wine process session import loader state

#### tracks modeled module refcounts and releases successful import loads

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tracks modeled module refcounts and releases successful import loads
   - Expected: result.ok is true
   - Expected: result.module_count equals `2`
   - Expected: result.loaded_count equals `2`
   - Expected: result.released_count equals `2`
   - Expected: result.rollback_count equals `0`
   - Expected: result.max_ref_count equals `2`
   - Expected: result.status equals `import-loader-state-planned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tracks modeled module refcounts and releases successful import loads")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_loader_state(plan, _known_hello_with_second_import_descriptor(), 4, 8)
expect(result.ok).to_equal(true)
expect(result.module_count).to_equal(2)
expect(result.loaded_count).to_equal(2)
expect(result.released_count).to_equal(2)
expect(result.rollback_count).to_equal(0)
expect(result.max_ref_count).to_equal(2)
expect(result.evidence).to_contain("import-loader-state-planned")
expect(result.evidence).to_contain("import-loader-refcounts-tracked")
expect(result.evidence).to_contain("import-loader-modules-loaded")
expect(result.evidence).to_contain("import-loader-modules-released")
expect(result.evidence).to_contain("import-loader-refcounts-restored")
expect(result.evidence).to_contain("no-real-dll-loaded")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("import-loader-state-planned")
```

</details>

#### rolls back modeled module loads when import resolution fails

- rolls back modeled module loads when import resolution fails
   - Expected: result.ok is false
   - Expected: result.error equals `import-proc-address:USER32.dll!DialogBoxW:proc-not-found`
   - Expected: result.module_count equals `2`
   - Expected: result.loaded_count equals `2`
   - Expected: result.released_count equals `0`
   - Expected: result.rollback_count equals `2`
   - Expected: result.max_ref_count equals `2`
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rolls back modeled module loads when import resolution fails")
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_loader_state(plan, _known_hello_with_missing_user32_proc(), 4, 8)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("import-proc-address:USER32.dll!DialogBoxW:proc-not-found")
expect(result.module_count).to_equal(2)
expect(result.loaded_count).to_equal(2)
expect(result.released_count).to_equal(0)
expect(result.rollback_count).to_equal(2)
expect(result.max_ref_count).to_equal(2)
expect(result.evidence).to_contain("import-loader-rollback-complete")
expect(result.evidence).to_contain("import-loader-refcounts-restored")
expect(result.evidence).to_contain("no-real-dll-loaded")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_loader_state_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine process session import loader state.
- Wine process session import loader state

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `82ea5852fad16cb52e0e5227a7210f2a29cf8cafaddd35fefe7811f928b21b15`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `82ea5852fad16cb52e0e5227a7210f2a29cf8cafaddd35fefe7811f928b21b15`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `82ea5852fad16cb52e0e5227a7210f2a29cf8cafaddd35fefe7811f928b21b15`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/wine_process_session_loader_state_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_process_session_loader_state_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_process_session_loader_state_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_process_session_loader_state_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_process_session_loader_state_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_process_session_loader_state_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks modeled module refcounts and releases successful import loads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_process_session_loader_state_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rolls back modeled module loads when import resolution fails' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
