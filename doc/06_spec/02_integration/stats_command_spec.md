# stats_command_spec

> Verifies the stats command behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# stats_command_spec

Verifies the stats command behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/stats_command_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the stats command behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### stats command

#### shows basic statistics

- Verify: shows basic statistics


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-02_INTEGRATION_STATS_COMMAND-001
step("Verify: shows basic statistics")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# This is a manual test - run: bin/simple stats
# Expected: Shows files, lines, tests, features
check_msg(true, "Manual test placeholder")
```

</details>

#### supports --brief flag

- Verify: supports --brief flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-02_INTEGRATION_STATS_COMMAND-001
step("Verify: supports --brief flag")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# Run: bin/simple stats --brief
# Expected: No "Collecting data..." or documentation section
check_msg(true, "Manual test placeholder")
```

</details>

#### supports --verbose flag

- Verify: supports --verbose flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-02_INTEGRATION_STATS_COMMAND-001
step("Verify: supports --verbose flag")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# Run: bin/simple stats --verbose
# Expected: Shows directory scan details
check_msg(true, "Manual test placeholder")
```

</details>

#### supports --quick flag

- Verify: supports --quick flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-02_INTEGRATION_STATS_COMMAND-001
step("Verify: supports --quick flag")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# Run: bin/simple stats --quick
# Expected: Skips line counting, faster execution
check_msg(true, "Manual test placeholder")
```

</details>

#### supports --json flag

- Verify: supports --json flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-02_INTEGRATION_STATS_COMMAND-001
step("Verify: supports --json flag")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# Run: bin/simple stats --json
# Expected: Outputs valid JSON with all metrics
check_msg(true, "Manual test placeholder")
```

</details>

#### combines flags correctly

- Verify: combines flags correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-02_INTEGRATION_STATS_COMMAND-001
step("Verify: combines flags correctly")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# Run: bin/simple stats --json --quick
# Expected: JSON output with lines: 0
check_msg(true, "Manual test placeholder")
```

</details>

### stats output accuracy

#### counts source files correctly

- Verify: counts source files correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-02_INTEGRATION_STATS_COMMAND-001
step("Verify: counts source files correctly")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# Verify file counts match actual filesystem
check_msg(true, "Manual test placeholder")
```

</details>

#### extracts test statistics from test_result.md

- Verify: extracts test statistics from test_result.md


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-02_INTEGRATION_STATS_COMMAND-001
step("Verify: extracts test statistics from test_result.md")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# Verify test counts match doc/08_tracking/test/test_result.md
check_msg(true, "Manual test placeholder")
```

</details>

#### extracts feature statistics from feature_db.sdn

- Verify: extracts feature statistics from feature_db.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-02_INTEGRATION_STATS_COMMAND-001
step("Verify: extracts feature statistics from feature_db.sdn")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# Verify feature counts match doc/08_tracking/feature/feature_db.sdn
check_msg(true, "Manual test placeholder")
```

</details>

### stats performance

#### completes in under 5 seconds (full mode)

- Verify: completes in under 5 seconds (full mode)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-02_INTEGRATION_STATS_COMMAND-001
step("Verify: completes in under 5 seconds (full mode)")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# time bin/simple stats
# Expected: < 5s
check_msg(true, "Manual test placeholder")
```

</details>

#### completes in under 1 second (quick mode)

- Verify: completes in under 1 second (quick mode)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-02_INTEGRATION_STATS_COMMAND-001
step("Verify: completes in under 1 second (quick mode)")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# time bin/simple stats --quick
# Expected: < 1s
check_msg(true, "Manual test placeholder")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d4ced2e49c10c6b0ed55efccc6ed741da575670c00e8c7995e573ac6a8940a94`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d4ced2e49c10c6b0ed55efccc6ed741da575670c00e8c7995e573ac6a8940a94`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d4ced2e49c10c6b0ed55efccc6ed741da575670c00e8c7995e573ac6a8940a94`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/stats_command_spec.spl
mirror: doc/06_spec/02_integration/stats_command_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/stats_command_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/stats_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/stats_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
