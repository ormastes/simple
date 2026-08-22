# green_spawn_deferred_spec

> Verifies the green spawn deferred behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# green_spawn_deferred_spec

Verifies the green spawn deferred behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the green spawn deferred behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### green_spawn deferred execution (E6)

#### spawn does not execute the body immediately

- Verify: spawn does not execute the body immediately
   - Expected: before_counter equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: after_spawn_counter equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-CONCURRENT_GREEN_SPAWN_DEFER-001
step("Verify: spawn does not execute the body immediately")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
DEFERRED_COUNTER = 0
val before_counter = DEFERRED_COUNTER
val handle = green_spawn(deferred_body_inc)
val after_spawn_counter = DEFERRED_COUNTER
# Body must not have run yet
expect(before_counter).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(after_spawn_counter).to_equal(0)  # oracle: pinned constant asserted by this scenario
# Queue has one pending task
val ready = green_ready_count()
assert_true(ready >= 1)
# Clean up
green_run_all()
```

</details>

#### run_one executes the deferred body and marks handle done

- Verify: run_one executes the deferred body and marks handle done
   - Expected: DEFERRED_COUNTER equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: DEFERRED_COUNTER equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: handle.join() equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-CONCURRENT_GREEN_SPAWN_DEFER-001
step("Verify: run_one executes the deferred body and marks handle done")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
DEFERRED_COUNTER = 0
val handle = green_spawn(deferred_body_inc)
expect_not(handle.is_done())
expect(DEFERRED_COUNTER).to_equal(0)  # oracle: pinned constant asserted by this scenario
val ran = green_run_one()
assert_true(ran)
expect(DEFERRED_COUNTER).to_equal(1)  # oracle: pinned constant asserted by this scenario
assert_true(handle.is_done())
expect(handle.join()).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### all deferred tasks execute on run_all and counter reaches N

- Verify: all deferred tasks execute on run_all and counter reaches N
   - Expected: DEFERRED_COUNTER equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: DEFERRED_COUNTER equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-CONCURRENT_GREEN_SPAWN_DEFER-001
step("Verify: all deferred tasks execute on run_all and counter reaches N")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
DEFERRED_COUNTER = 0
val h1 = green_spawn(deferred_body_inc)
val h2 = green_spawn(deferred_body_inc)
val h3 = green_spawn(deferred_body_inc)
# None have run yet
expect(DEFERRED_COUNTER).to_equal(0)  # oracle: pinned constant asserted by this scenario
val ran = green_run_all()
assert_true(ran >= 3)
expect(DEFERRED_COUNTER).to_equal(3)  # oracle: pinned constant asserted by this scenario
assert_true(h1.is_done())
assert_true(h2.is_done())
assert_true(h3.is_done())
```

</details>

#### a task with bad result does not stop sibling tasks

- Verify: a task with bad result does not stop sibling tasks
   - Expected: SIBLING_RAN equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: SIBLING_RAN equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: h_sibling1.join() equals `77)  # oracle: pinned constant asserted by this scenario`
   - Expected: h_sibling2.join() equals `77)  # oracle: pinned constant asserted by this scenario`
   - Expected: bad_result equals `-99)  # oracle: pinned constant asserted by this scenario`
   - Expected: err_reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-CONCURRENT_GREEN_SPAWN_DEFER-001
step("Verify: a task with bad result does not stop sibling tasks")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
SIBLING_RAN = 0
val h_bad = green_spawn(bad_result_body)
val h_sibling1 = green_spawn(sibling_body)
val h_sibling2 = green_spawn(sibling_body)
# None have run yet
expect(SIBLING_RAN).to_equal(0)  # oracle: pinned constant asserted by this scenario
green_run_all()
# Siblings must have run despite bad_result_body
expect(SIBLING_RAN).to_equal(2)  # oracle: pinned constant asserted by this scenario
assert_true(h_sibling1.is_done())
assert_true(h_sibling2.is_done())
expect(h_sibling1.join()).to_equal(77)  # oracle: pinned constant asserted by this scenario
expect(h_sibling2.join()).to_equal(77)  # oracle: pinned constant asserted by this scenario
# bad task is also done, result is the sentinel
assert_true(h_bad.is_done())
val bad_result = h_bad.join()
expect(bad_result).to_equal(-99)  # oracle: pinned constant asserted by this scenario
# green_task_error returns empty for non-fatal value-level "error"
val err_reason = green_task_error(h_bad.id())
expect(err_reason).to_equal("")
```

</details>

#### green_fail marks the task errored and green_task_error returns the reason

- Verify: green_fail marks the task errored and green_task_error returns the reason
   - Expected: h_sibling.join() equals `77)  # oracle: pinned constant asserted by this scenario`
   - Expected: reason equals `failing_body: deliberate failure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-CONCURRENT_GREEN_SPAWN_DEFER-001
step("Verify: green_fail marks the task errored and green_task_error returns the reason")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h_fail = green_spawn(failing_body)
val h_sibling = green_spawn(sibling_body)
green_run_all()
assert_true(h_fail.is_done())
assert_true(h_sibling.is_done())
# Sibling must be unaffected by the failing task.
expect(h_sibling.join()).to_equal(77)  # oracle: pinned constant asserted by this scenario
val reason = green_task_error(h_fail.id())
expect(reason).to_equal("failing_body: deliberate failure")
```

</details>

#### green_task_error returns empty for a task that never called green_fail

- Verify: green_task_error returns empty for a task that never called green_fail
   - Expected: green_task_error(h_ok.id()) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-CONCURRENT_GREEN_SPAWN_DEFER-001
step("Verify: green_task_error returns empty for a task that never called green_fail")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h_ok = green_spawn(deferred_body_inc)
green_run_all()
assert_true(h_ok.is_done())
expect(green_task_error(h_ok.id())).to_equal("")
```

</details>

#### green_spawn_value still works alongside deferred tasks

- Verify: green_spawn_value still works alongside deferred tasks
   - Expected: h_value.join() equals `55)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-CONCURRENT_GREEN_SPAWN_DEFER-001
step("Verify: green_spawn_value still works alongside deferred tasks")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val h_value = green_spawn_value(55)
val h_deferred = green_spawn(deferred_body_inc)
expect_not(h_value.is_done())
expect_not(h_deferred.is_done())
green_run_all()
assert_true(h_value.is_done())
assert_true(h_deferred.is_done())
expect(h_value.join()).to_equal(55)  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c859a58517a216b304580e4db7e962227411bc153a617e038e5ba8465111fdb6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c859a58517a216b304580e4db7e962227411bc153a617e038e5ba8465111fdb6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c859a58517a216b304580e4db7e962227411bc153a617e038e5ba8465111fdb6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
