# Duplicate Check Contract Specification

> Tests covering duplicate-check CLI contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Duplicate Check Contract Specification

## Scenarios

### duplicate-check CLI contract

#### scans an excluded fixture when --no-default-excludes is set

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- scans an excluded fixture when --no-default-excludes is set
   - Expected: result.exit_code equals `1`
   - Expected: result.stdout does not contain `Found 0 duplicate groups`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("scans an excluded fixture when --no-default-excludes is set")
val simple = simple_binary()
val result = run_duplicate_check(simple, "test/fixtures/duplication/dup_pair")

# Bounded-time: `timeout 60` kills a runaway process with exit code
# 124. On these two tiny fixture files, the token-mode scan must
# finish well inside that budget.
assert_not_equal(result.exit_code, 124)

expect(result.exit_code).to_equal(1)
expect(result.stdout).to_contain("duplicate groups")
expect(result.stdout.contains("Found 0 duplicate groups")).to_equal(false)
```

</details>

#### reports silence for a scratch copy of clean_pair (exit 0)

- reports silence for a scratch copy of clean_pair (exit 0)
   - Expected: stage_fixture(scratch_dir, "test/fixtures/duplication/clean_pair") equals `0`
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports silence for a scratch copy of clean_pair (exit 0)")
val simple = simple_binary()
val scratch_dir = "/tmp/duplicate_check_contract_clean_pair"
expect(stage_fixture(scratch_dir, "test/fixtures/duplication/clean_pair")).to_equal(0)

val result = run_duplicate_check(simple, scratch_dir)

assert_not_equal(result.exit_code, 124)

expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("Found 0 duplicate groups")
```

</details>

#### rejects unknown or malformed options before scanning their values

- rejects unknown or malformed options before scanning their values
   - Expected: result.exit_code equals `2`
   - Expected: malformed.exit_code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects unknown or malformed options before scanning their values")
val simple = simple_binary()
val result = shell("timeout 60 {simple} run src/compiler/90.tools/duplicate_check/main.spl -- --bogus test/fixtures/duplication/clean_pair --mode token --format json")

assert_not_equal(result.exit_code, 124)
expect(result.exit_code).to_equal(2)
expect(result.stdout).to_contain("Usage: simple duplicate-check <path> [options]")

val malformed = shell("timeout 60 {simple} run src/compiler/90.tools/duplicate_check/main.spl -- test/fixtures/duplication/clean_pair --token=garbage --format json")
expect(malformed.exit_code).to_equal(2)
expect(malformed.stdout).to_contain("Usage: simple duplicate-check <path> [options]")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/cli/duplicate_check_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering duplicate-check CLI contract.
- duplicate-check CLI contract

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ad30783633bc43cdce220fa30c7c16bb5829547d56714f4b995c5c8a81ec25b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ad30783633bc43cdce220fa30c7c16bb5829547d56714f4b995c5c8a81ec25b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ad30783633bc43cdce220fa30c7c16bb5829547d56714f4b995c5c8a81ec25b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/cli/duplicate_check_contract_spec.spl
mirror: doc/06_spec/03_system/app/cli/duplicate_check_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/cli/duplicate_check_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/cli/duplicate_check_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/cli/duplicate_check_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/cli/duplicate_check_contract_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scans an excluded fixture when --no-default-excludes is set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/cli/duplicate_check_contract_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports silence for a scratch copy of clean_pair (exit 0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/cli/duplicate_check_contract_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unknown or malformed options before scanning their values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
