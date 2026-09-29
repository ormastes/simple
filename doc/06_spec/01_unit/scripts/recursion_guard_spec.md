# recursion_guard_spec

> As a maintainer landing through check scripts that fork other check

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# recursion_guard_spec

As a maintainer landing through check scripts that fork other check

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/scripts/recursion_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

As a maintainer landing through check scripts that fork other check
    scripts, I want a script that ends up re-invoking itself to be refused
    at a bounded depth with exit 3 and one clear FAIL line, so a recursion
    bug cannot fork-bomb the shared box.

## Scenarios

### recursion guard for .shs scripts

#### the guard's own --selftest passes with a PASS verdict line

- the guard's own --selftest passes with a PASS verdict line
- Run sh " + GUARD + " --selftest and capture exit code plus last stdout line
- Exit code is 0
- Verdict line names a non-zero fixture count


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the guard's own --selftest passes with a PASS verdict line")
step("Run sh " + GUARD + " --selftest and capture exit code plus last stdout line")
val out = process_run("sh", ["-c",
    "o=$(sh " + GUARD + " --selftest); rc=$?; " +
    "last=$(printf '%s\\n' \"$o\" | tail -1); echo \"RC=$rc LAST=$last\""])
val s: text = out.0
step("Exit code is 0")
expect(s).to_contain("RC=0")
step("Verdict line names a non-zero fixture count")
expect(s).to_contain("LAST=recursion-guard selftest: PASS — 4 fixture(s)")
```

</details>

#### a self-invoking script is refused with exit 3 and the FAIL line

- a self-invoking script is refused with exit 3 and the FAIL line
- Write a fixture that sources the guard then re-executes itself
- Exit code is 3 — the recursion-guard refusal code
- The FAIL line names the script, the depth, and the override knob


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a self-invoking script is refused with exit 3 and the FAIL line")
step("Write a fixture that sources the guard then re-executes itself")
val out = process_run("sh", ["-c",
    "mkdir -p " + TMP_PARENT + "; d=$(mktemp -d " + TMP_PARENT + "/rg_spec.XXXXXX); " +
    "g=$(pwd)/" + GUARD + "; " +
    "printf '. \"%s\"\\nexec sh \"$0\"\\n' \"$g\" > $d/loop.shs; " +
    "err=$(env -u SIMPLE_SHS_DEPTH -u SIMPLE_SHS_MAX_DEPTH sh $d/loop.shs 2>&1 >/dev/null); rc=$?; " +
    "rm -rf $d; echo \"RC=$rc ERR=$err\""])
val s: text = out.0
step("Exit code is 3 — the recursion-guard refusal code")
expect(s).to_contain("RC=3")
step("The FAIL line names the script, the depth, and the override knob")
expect(s).to_contain("ERR=recursion-guard: FAIL — loop.shs refused at depth 3 (max 3); set SIMPLE_SHS_MAX_DEPTH to raise")
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

- Canonical SPipe generation for source `f93d3e2e62d2977db57e1ed6b23bfd9bfe199803c27e5b2e135cf9ca86836c80`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f93d3e2e62d2977db57e1ed6b23bfd9bfe199803c27e5b2e135cf9ca86836c80`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f93d3e2e62d2977db57e1ed6b23bfd9bfe199803c27e5b2e135cf9ca86836c80`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/scripts/recursion_guard_spec.spl
mirror: doc/06_spec/01_unit/scripts/recursion_guard_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/scripts/recursion_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/scripts/recursion_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/scripts/recursion_guard_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the guard's own --selftest passes with a PASS verdict line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/scripts/recursion_guard_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a self-invoking script is refused with exit 3 and the FAIL line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
