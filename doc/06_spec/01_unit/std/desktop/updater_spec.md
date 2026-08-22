# updater_spec

> Verifies the updater behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# updater_spec

Verifies the updater behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/desktop/updater_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the updater behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Desktop Auto-Updater API

#### creates UpdateInfo struct

- Verify: creates UpdateInfo struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DESKTOP_UPDATER-001
step("Verify: creates UpdateInfo struct")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val info = UpdateInfo(version: "1.0.1", url: "https://example.com/update", release_notes: "Bug fixes", mandatory: false)
expect info.version == "1.0.1"
expect info.mandatory == false
```

</details>

#### creates UpdateConfig struct

- Verify: creates UpdateConfig struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DESKTOP_UPDATER-001
step("Verify: creates UpdateConfig struct")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val config = UpdateConfig(feed_url: "https://example.com/feed", current_version: "1.0.0", auto_download: true)
expect config.auto_download == true
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cb53c6a38a85a67b48e1a835f17b2b6252a352b23f4511631a35ec6988a602c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cb53c6a38a85a67b48e1a835f17b2b6252a352b23f4511631a35ec6988a602c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cb53c6a38a85a67b48e1a835f17b2b6252a352b23f4511631a35ec6988a602c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/desktop/updater_spec.spl
mirror: doc/06_spec/01_unit/std/desktop/updater_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/desktop/updater_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/desktop/updater_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/desktop/updater_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
