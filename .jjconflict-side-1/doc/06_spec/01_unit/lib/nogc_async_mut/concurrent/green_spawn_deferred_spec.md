# Green Spawn Deferred Specification

> Tests covering green_spawn deferred execution (E6).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Green Spawn Deferred Specification

## Scenarios

### green_spawn deferred execution (E6)

#### spawn does not execute the body immediately

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- spawn does not execute the body immediately
   - Expected: before_counter equals `0`
   - Expected: after_spawn_counter equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("spawn does not execute the body immediately")
DEFERRED_COUNTER = 0
val before_counter = DEFERRED_COUNTER
val handle = green_spawn(deferred_body_inc)
val after_spawn_counter = DEFERRED_COUNTER
# Body must not have run yet
expect(before_counter).to_equal(0)
expect(after_spawn_counter).to_equal(0)
# Queue has one pending task
val ready = green_ready_count()
assert_true(ready >= 1)
# Clean up
green_run_all()
```

</details>

#### run_one executes the deferred body and marks handle done

- run_one executes the deferred body and marks handle done
   - Expected: DEFERRED_COUNTER equals `0`
   - Expected: DEFERRED_COUNTER equals `1`
   - Expected: handle.join() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("run_one executes the deferred body and marks handle done")
DEFERRED_COUNTER = 0
val handle = green_spawn(deferred_body_inc)
expect_not(handle.is_done())
expect(DEFERRED_COUNTER).to_equal(0)
val ran = green_run_one()
assert_true(ran)
expect(DEFERRED_COUNTER).to_equal(1)
assert_true(handle.is_done())
expect(handle.join()).to_equal(1)
```

</details>

#### all deferred tasks execute on run_all and counter reaches N

- all deferred tasks execute on run_all and counter reaches N
   - Expected: DEFERRED_COUNTER equals `0`
   - Expected: DEFERRED_COUNTER equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("all deferred tasks execute on run_all and counter reaches N")
DEFERRED_COUNTER = 0
val h1 = green_spawn(deferred_body_inc)
val h2 = green_spawn(deferred_body_inc)
val h3 = green_spawn(deferred_body_inc)
# None have run yet
expect(DEFERRED_COUNTER).to_equal(0)
val ran = green_run_all()
assert_true(ran >= 3)
expect(DEFERRED_COUNTER).to_equal(3)
assert_true(h1.is_done())
assert_true(h2.is_done())
assert_true(h3.is_done())
```

</details>

#### a task with bad result does not stop sibling tasks

- a task with bad result does not stop sibling tasks
   - Expected: SIBLING_RAN equals `0`
   - Expected: SIBLING_RAN equals `2`
   - Expected: h_sibling1.join() equals `77`
   - Expected: h_sibling2.join() equals `77`
   - Expected: bad_result equals `-99`
   - Expected: err_reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a task with bad result does not stop sibling tasks")
SIBLING_RAN = 0
val h_bad = green_spawn(bad_result_body)
val h_sibling1 = green_spawn(sibling_body)
val h_sibling2 = green_spawn(sibling_body)
# None have run yet
expect(SIBLING_RAN).to_equal(0)
green_run_all()
# Siblings must have run despite bad_result_body
expect(SIBLING_RAN).to_equal(2)
assert_true(h_sibling1.is_done())
assert_true(h_sibling2.is_done())
expect(h_sibling1.join()).to_equal(77)
expect(h_sibling2.join()).to_equal(77)
# bad task is also done, result is the sentinel
assert_true(h_bad.is_done())
val bad_result = h_bad.join()
expect(bad_result).to_equal(-99)
# green_task_error returns empty for non-fatal value-level "error"
val err_reason = green_task_error(h_bad.id())
expect(err_reason).to_equal("")
```

</details>

#### green_fail marks the task errored and green_task_error returns the reason

- green_fail marks the task errored and green_task_error returns the reason
   - Expected: h_sibling.join() equals `77`
   - Expected: reason equals `failing_body: deliberate failure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("green_fail marks the task errored and green_task_error returns the reason")
val h_fail = green_spawn(failing_body)
val h_sibling = green_spawn(sibling_body)
green_run_all()
assert_true(h_fail.is_done())
assert_true(h_sibling.is_done())
# Sibling must be unaffected by the failing task.
expect(h_sibling.join()).to_equal(77)
val reason = green_task_error(h_fail.id())
expect(reason).to_equal("failing_body: deliberate failure")
```

</details>

#### green_task_error returns empty for a task that never called green_fail

- green_task_error returns empty for a task that never called green_fail
   - Expected: green_task_error(h_ok.id()) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("green_task_error returns empty for a task that never called green_fail")
val h_ok = green_spawn(deferred_body_inc)
green_run_all()
assert_true(h_ok.is_done())
expect(green_task_error(h_ok.id())).to_equal("")
```

</details>

#### green_spawn_value still works alongside deferred tasks

- green_spawn_value still works alongside deferred tasks
   - Expected: h_value.join() equals `55`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("green_spawn_value still works alongside deferred tasks")
val h_value = green_spawn_value(55)
val h_deferred = green_spawn(deferred_body_inc)
expect_not(h_value.is_done())
expect_not(h_deferred.is_done())
green_run_all()
assert_true(h_value.is_done())
assert_true(h_deferred.is_done())
expect(h_value.join()).to_equal(55)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering green_spawn deferred execution (E6).
- green_spawn deferred execution (E6)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `80e277523e6c6b2e334623c31c233eb8685ac9007f61c913f58711b8d5fcc3a8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `80e277523e6c6b2e334623c31c233eb8685ac9007f61c913f58711b8d5fcc3a8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `80e277523e6c6b2e334623c31c233eb8685ac9007f61c913f58711b8d5fcc3a8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'spawn does not execute the body immediately' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'run_one executes the deferred body and marks handle done' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all deferred tasks execute on run_all and counter reaches N' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
