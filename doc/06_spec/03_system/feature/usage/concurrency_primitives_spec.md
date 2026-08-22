# @manual: primary

> Purpose: Prove that Concurrency Primitives.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that Concurrency Primitives.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | Active |
| Source | `test/03_system/feature/usage/concurrency_primitives_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Concurrency Primitives.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-FEATURE-CONCURRENCY-PRIMITIV-001
doc/01_research/feature/REQ-FEATURE-CONCURRENCY-PRIMITIV-001.md
doc/03_plan/feature/REQ-FEATURE-CONCURRENCY-PRIMITIV-001.md
doc/04_architecture/feature/REQ-FEATURE-CONCURRENCY-PRIMITIV-001.md
doc/05_design/feature/REQ-FEATURE-CONCURRENCY-PRIMITIV-001.md

## Scenarios

### Concurrency Primitives

#### Futures

#### executes a spawned task to completion when the scheduler runs

- Spawn a task and drive it through green_run_one


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-CONCURRENCY-PRIMITIV-001
step("Spawn a task and drive it through green_run_one")
val before = CP_SEEN
val handle = green_spawn(cp_task)
assert_true(not handle.is_done())
assert_equal(green_run_one(), true)
assert_true(handle.is_done())
assert_equal(handle.join(), 21)
assert_equal(CP_SEEN - before, 1)
```

</details>

#### Value futures

#### resolves a pre-computed future without a scheduler step

- Create a green_spawn_value future and resolve it with run_one


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-CONCURRENCY-PRIMITIV-001
step("Create a green_spawn_value future and resolve it with run_one")
val handle = green_spawn_value(42)
assert_equal(green_run_one(), true)
assert_true(handle.is_done())
assert_equal(handle.join(), 42)
```

</details>

#### Concurrent execution

#### runs every queued task to completion with green_run_all

- Queue three tasks then drain them with green_run_all


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-CONCURRENCY-PRIMITIV-001
step("Queue three tasks then drain them with green_run_all")
val before = CP_SEEN
val h1 = green_spawn(cp_task)
val h2 = green_spawn(cp_task)
val h3 = green_spawn(cp_task)
val ran = green_run_all()
assert_equal(CP_SEEN - before, 3)
assert_true(h1.is_done() and h2.is_done() and h3.is_done())
assert_equal(h1.id() != h2.id(), true)
```

</details>

#### Error handling in async

#### captures a failed task's reason for the caller

- Run a failing task and read green_task_error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-FEATURE-CONCURRENCY-PRIMITIV-001
step("Run a failing task and read green_task_error")
val handle = green_spawn(cp_failing_task)
assert_equal(green_run_one(), true)
assert_true(handle.is_done())
assert_equal(green_task_error(handle.id()),
    "concurrency-primitives probe failure")
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

- Canonical SPipe generation for source `29e2dbe005699b81f66a46718995a45a040341fc2573f873ceb921a362021b0b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `29e2dbe005699b81f66a46718995a45a040341fc2573f873ceb921a362021b0b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `29e2dbe005699b81f66a46718995a45a040341fc2573f873ceb921a362021b0b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/usage/concurrency_primitives_spec.spl
mirror: doc/06_spec/03_system/feature/usage/concurrency_primitives_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/concurrency_primitives_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/feature/usage/concurrency_primitives_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/concurrency_primitives_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/concurrency_primitives_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes a spawned task to completion when the scheduler runs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/concurrency_primitives_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a pre-computed future without a scheduler step' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/concurrency_primitives_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs every queued task to completion with green_run_all' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
