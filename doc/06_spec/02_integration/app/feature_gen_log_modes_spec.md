# feature_gen_log_modes_spec

> Purpose: shows shared log options in help

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# feature_gen_log_modes_spec

Purpose: shows shared log options in help

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/feature_gen_log_modes_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Operator workflow
## Compatibility and limitations

## Purpose and audience
Purpose: shows shared log options in help
Audience: compiler and tooling engineers who maintain this spec

## Scenarios

### feature-gen log mode CLI options

#### shows shared log options in help

- Verify: shows shared log options in help
   - Expected: code equals `0)  # oracle: value fixed by the spec contract  # oracle: pinned constant ass... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Verify: shows shared log options in help")
# @req: REQ-APP-FeatGenLogMode-001
_setup_fixture()
val (out, err, code) = _run_feature_gen(["--help"])
expect(code).to_equal(0)  # oracle: value fixed by the spec contract  # oracle: pinned constant asserted by this scenario
expect(out).to_contain("--log-mode")
expect(out).to_contain("--progress")
```

</details>

#### supports log-mode json

- Verify: supports log-mode json
   - Expected: code equals `0)  # oracle: value fixed by the spec contract  # oracle: pinned constant ass... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Verify: supports log-mode json")
# @req: REQ-APP-FeatGenLogMode-001
_setup_fixture()
val (out, err, code) = _run_feature_gen(["--log-mode=json"])
expect(code).to_equal(0)  # oracle: value fixed by the spec contract  # oracle: pinned constant asserted by this scenario
expect(out).to_contain("\"command\":\"feature-gen\"")
expect(out).to_contain("\"status\":\"ok\"")
expect(out).to_contain("\"features\":2")
```

</details>

#### supports dot progress

- Verify: supports dot progress
   - Expected: code equals `0)  # oracle: value fixed by the spec contract  # oracle: pinned constant ass... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Verify: supports dot progress")
# @req: REQ-APP-FeatGenLogMode-001
_setup_fixture()
val (out, err, code) = _run_feature_gen(["--progress=dot"])
expect(code).to_equal(0)  # oracle: value fixed by the spec contract  # oracle: pinned constant asserted by this scenario
expect(out).to_contain(".")
expect(out).to_contain("Done. Generated tracking docs for 2 features")
```

</details>

#### rejects invalid log mode

- Verify: rejects invalid log mode
   - Expected: code equals `1)  # oracle: value fixed by the spec contract  # oracle: pinned constant ass... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Verify: rejects invalid log mode")
# @req: REQ-APP-FeatGenLogMode-001
_setup_fixture()
val (out, err, code) = _run_feature_gen(["--log-mode=noisy"])
expect(code).to_equal(1)  # oracle: value fixed by the spec contract  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3abfef4655c6e2fbc6930c166bbdf151024a3dbe557191ae389c00b1db7e3d77`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3abfef4655c6e2fbc6930c166bbdf151024a3dbe557191ae389c00b1db7e3d77`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3abfef4655c6e2fbc6930c166bbdf151024a3dbe557191ae389c00b1db7e3d77`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/app/feature_gen_log_modes_spec.spl
mirror: doc/06_spec/02_integration/app/feature_gen_log_modes_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/feature_gen_log_modes_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/app/feature_gen_log_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/feature_gen_log_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
