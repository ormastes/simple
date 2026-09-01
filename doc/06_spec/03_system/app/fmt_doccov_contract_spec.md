# Fmt Doccov Contract Specification

> Tests covering simple fmt CLI contract (pure-Simple standalone entry), simple doc-coverage CLI contract (pure-Simple standalone entry).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fmt Doccov Contract Specification

## Scenarios

### simple fmt CLI contract (pure-Simple standalone entry)

#### exits nonzero on --check against a file with real violations

- exits nonzero on --check against a file with real violations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exits nonzero on --check against a file with real violations")
val (stdout, stderr, code) = _cli_process_run(SIMPLE_SEED, ["run", FMT_ENTRY, FMT_FIXTURE, "--check"])
assert_not_equal(code, 0)
assert_contains(stdout, "needs formatting")
```

</details>

#### writes, then reports formatted on re-check, and is idempotent on a second write

- writes, then reports formatted on re-check, and is idempotent on a second write


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes, then reports formatted on re-check, and is idempotent on a second write")
val setup = _cli_process_run("cp", [FMT_FIXTURE, SCRATCH])
assert_equal(setup.2, 0)

val (write_out, write_err, write_code) = _cli_process_run(SIMPLE_SEED, ["run", FMT_ENTRY, SCRATCH, "--write"])
assert_equal(write_code, 0)
assert_contains(write_out, "OK Formatted")

val (check_out, check_err, check_code) = _cli_process_run(SIMPLE_SEED, ["run", FMT_ENTRY, SCRATCH, "--check"])
assert_equal(check_code, 0)
assert_contains(check_out, "is formatted")

val scratch_after_write1 = SCRATCH + ".after1"
val snapshot = _cli_process_run("cp", [SCRATCH, scratch_after_write1])
assert_equal(snapshot.2, 0)

val (write2_out, write2_err, write2_code) = _cli_process_run(SIMPLE_SEED, ["run", FMT_ENTRY, SCRATCH, "--write"])
assert_equal(write2_code, 0)

val idempotence_check = _cli_process_run("diff", [scratch_after_write1, SCRATCH])
assert_equal(idempotence_check.2, 0)
```

</details>

### simple doc-coverage CLI contract (pure-Simple standalone entry)

#### reports the undocumented pub fn and exits 0

- reports the undocumented pub fn and exits 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports the undocumented pub fn and exits 0")
val (stdout, stderr, code) = _cli_process_run(SIMPLE_SEED, ["run", DOC_COVERAGE_ENTRY, DOC_COVERAGE_FIXTURE_DIR, "--missing"])
assert_equal(code, 0)
assert_contains(stdout, "orphan_fn")
```

</details>

#### does not list the already-documented pub fn as missing

- does not list the already-documented pub fn as missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not list the already-documented pub fn as missing")
# `orphan_fn` and `documented_thing` deliberately share no substring
# with each other, so this check cannot pass vacuously: if
# print_missing regresses to listing every `pub fn` match again (the
# 2026-07-17 bug), "documented_thing" reappears in stdout and this
# example genuinely fails.
val (stdout, stderr, code) = _cli_process_run(SIMPLE_SEED, ["run", DOC_COVERAGE_ENTRY, DOC_COVERAGE_FIXTURE_DIR, "--missing"])
assert_false(stdout.contains("documented_thing"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/fmt_doccov_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simple fmt CLI contract (pure-Simple standalone entry), simple doc-coverage CLI contract (pure-Simple standalone entry).
- simple fmt CLI contract (pure-Simple standalone entry)
- simple doc-coverage CLI contract (pure-Simple standalone entry)

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8a1fd898768a9d2da5b000f04f7dabee403f52969022f06c90b73d1d696fa679`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8a1fd898768a9d2da5b000f04f7dabee403f52969022f06c90b73d1d696fa679`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8a1fd898768a9d2da5b000f04f7dabee403f52969022f06c90b73d1d696fa679`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/fmt_doccov_contract_spec.spl
mirror: doc/06_spec/03_system/app/fmt_doccov_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/fmt_doccov_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/fmt_doccov_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/fmt_doccov_contract_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exits nonzero on --check against a file with real violations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/fmt_doccov_contract_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes, then reports formatted on re-check, and is idempotent on a second write' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/fmt_doccov_contract_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the undocumented pub fn and exits 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
