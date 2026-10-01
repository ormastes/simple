# Cts Corpus Spirv Binary Specification

> Tests covering board Vulkan conformance corpus (spirv_binary boundary).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cts Corpus Spirv Binary Specification

## Scenarios

### board Vulkan conformance corpus (spirv_binary boundary)

#### declares a non-empty corpus with a deliberately hostile mix

- load the declared case list
- confirm at least one case is marked non_correspond up front
- confirm at least one case is flagged hostile


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("load the declared case list")
val cases = board_vulkan_corpus()
assert_true(cases.len() >= 7)

step("confirm at least one case is marked non_correspond up front")
var non_correspond_count = 0
for case in cases:
    if case.expected_relation == "non_correspond":
        non_correspond_count = non_correspond_count + 1
assert_true(non_correspond_count >= 1)

step("confirm at least one case is flagged hostile")
var hostile_count = 0
for case in cases:
    if case.hostile:
        hostile_count = hostile_count + 1
assert_true(hostile_count >= 1)
```

</details>

#### executes every declared case and produces a verdict for each

- run the full corpus through the executor
- confirm the deliberately corrupt case is confirmed non-corresponding, not forced to pass
- confirm every case produced an accepted verdict shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("run the full corpus through the executor")
val (executed_ids, verdicts) = run_full_corpus()
val cases = board_vulkan_corpus()
assert_equal(executed_ids.len(), cases.len())
assert_equal(verdicts.len(), cases.len())

step("confirm the deliberately corrupt case is confirmed non-corresponding, not forced to pass")
var corrupt_verdict = ""
for v in verdicts:
    if v.case_id == "spirv_binary.deliberately_corrupt":
        corrupt_verdict = v.verdict
assert_equal(corrupt_verdict, "non_correspond_confirmed")

step("confirm every case produced an accepted verdict shape")
for v in verdicts:
    assert_true(case_verdict_is_ok(v))
```

</details>

#### passes the ledger when declared, executed, and skipped are fully accounted for

- build a ledger from a complete accounting


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build a ledger from a complete accounting")
val cases = board_vulkan_corpus()
var declared_ids: [text] = []
for case in cases:
    declared_ids = declared_ids + [case.case_id]
val (executed_ids, verdicts) = run_full_corpus()
var verdict_ids: [text] = []
for v in verdicts:
    verdict_ids = verdict_ids + [v.case_id]

val report = build_ledger(declared_ids, executed_ids, [], verdict_ids)
assert_true(report.ok)
assert_equal(report.declared, cases.len())
assert_equal(report.executed, cases.len())
assert_equal(report.skipped, 0)
assert_equal(report.no_verdict, 0)
```

</details>

#### SABOTAGE (a): fails the ledger when a declared case is dropped from execution

- declare 3 cases but only execute 2, dropping the third silently


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("declare 3 cases but only execute 2, dropping the third silently")
val declared_ids = ["case_a", "case_b", "case_c"]
val executed_ids = ["case_a", "case_b"]
val verdict_ids = ["case_a", "case_b"]
val report = build_ledger(declared_ids, executed_ids, [], verdict_ids)
assert_false(report.ok)
assert_true(report.failure_reason.contains("case_c"))
```

</details>

#### SABOTAGE (b): fails the ledger when a skip carries an empty reason

- skip a declared case with a blank reason string


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("skip a declared case with a blank reason string")
val declared_ids = ["case_a", "case_b"]
val executed_ids = ["case_a"]
val skips = [SkipEntry(case_id: "case_b", reason: "")]
val report = build_ledger(declared_ids, executed_ids, skips, ["case_a"])
assert_false(report.ok)
assert_true(report.failure_reason.contains("empty skip reason"))
```

</details>

#### SABOTAGE (c): fails the ledger when the corpus executes zero cases

- declare cases, skip every one of them, executing none


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("declare cases, skip every one of them, executing none")
val declared_ids = ["case_a", "case_b"]
val skips = [
    SkipEntry(case_id: "case_a", reason: "tool unavailable on this host"),
    SkipEntry(case_id: "case_b", reason: "tool unavailable on this host")
]
val report = build_ledger(declared_ids, [], skips, [])
assert_false(report.ok)
assert_true(report.failure_reason.contains("zero executed"))
```

</details>

#### restores to a clean pass after each sabotage proof, proving the ledger is not stuck red

- re-run the full, correctly-accounted ledger one more time


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("re-run the full, correctly-accounted ledger one more time")
val cases = board_vulkan_corpus()
var declared_ids: [text] = []
for case in cases:
    declared_ids = declared_ids + [case.case_id]
val (executed_ids, verdicts) = run_full_corpus()
var verdict_ids: [text] = []
for v in verdicts:
    verdict_ids = verdict_ids + [v.case_id]
val report = build_ledger(declared_ids, executed_ids, [], verdict_ids)
assert_true(report.ok)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/vulkan/cts_corpus_spirv_binary_spec.spl` |
| Updated | 2026-08-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering board Vulkan conformance corpus (spirv_binary boundary).
- board Vulkan conformance corpus (spirv_binary boundary)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
