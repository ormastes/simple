# SimpleOS Cooperative Green System Contract

> This system spec proves that the implemented cooperative-green API remains usable in the SimpleOS feature lane while preserving its explicit semantics: it queues logical work on the current carrier and does not claim CPU-parallel M:N execution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Cooperative Green System Contract

This system spec proves that the implemented cooperative-green API remains usable in the SimpleOS feature lane while preserving its explicit semantics: it queues logical work on the current carrier and does not claim CPU-parallel M:N execution.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-simpleos-cooperative |
| Category | SimpleOS / Concurrency |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/04_architecture/runtime/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec proves that the implemented cooperative-green API remains
usable in the SimpleOS feature lane while preserving its explicit semantics: it
queues logical work on the current carrier and does not claim CPU-parallel M:N
execution.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/04_architecture/runtime/multicore_green.md

## Research

**Research:** doc/01_research/local/multicore_green.md

## Syntax

Run the hosted SimpleOS cooperative-green contract:

```sh
./src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl --mode=interpreter --clean
```

## Examples

The scenarios prove that `cooperative_green_spawn` and
`cooperative_green_spawn_value` queue logical work on the current carrier,
remain pending before the carrier runs, and return their values after
`cooperative_green_run_one` or `cooperative_green_run_all`. This is current
carrier cooperative scheduling, not CPU-parallel M:N execution.

## Scenario Walkthrough

### Pending Until Carrier Run

- Read the current cooperative ready queue depth.
- Queue one logical green task with `cooperative_green_spawn`.
- Assert the handle is not done before the carrier runs.
- Assert the ready queue depth increased by one.
- Run one cooperative carrier turn.
- Assert the handle is done, joins to the expected value twice, and an extra
  carrier turn is a safe no-op.

### Drain Current Carrier

- Read the current cooperative ready queue depth.
- Queue two logical green tasks.
- Assert both tasks are visible in the ready queue.
- Run all queued cooperative work on the current carrier.
- Assert at least two tasks ran.
- Join both handles and assert their expected values.

### Direct Value Scheduling

- Queue a direct value with `cooperative_green_spawn_value`.
- Assert the value handle remains pending before a carrier turn.
- Run one cooperative carrier turn.
- Join the value handle twice and assert the direct value is returned both
  times.

### Evidence Boundary Classification

- Read the SimpleOS evidence report and multicore-green design docs.
- Assert cooperative-green evidence is classified as current-carrier logical
  scheduling.
- Assert cooperative-green evidence is not used as runtime-pool or Go-like
  M:N CPU-parallel proof.

## Evidence Boundary

- This spec proves hosted SimpleOS compatibility for the cooperative-green
  public API.
- It intentionally does not claim multicore CPU parallelism.
- It keeps cooperative-green evidence separate from `multicore_green_spawn`
  and from OS-thread `thread_spawn` evidence.
- It is valid fast evidence for current-carrier logical scheduling.
- Go-like M:N claims require `multicore_green_spawn` runtime-pool evidence or
  SimpleOS scheduler/AP evidence, not this cooperative queue alone.

## Traceability Notes

- NFR boundary: `doc/02_requirements/nfr/multicore_green.md`.
- Detail design: `doc/05_design/multicore_green.md`.
- `cooperative_green_spawn` covers closure-style logical work.
- `cooperative_green_spawn_value` covers direct value fanout rows.
- `cooperative_green_ready_count` is used as queue-depth evidence.
- `cooperative_green_run_one` proves one carrier turn.
- `cooperative_green_run_all` proves queue draining.
- The checked values `3`, `8`, and `21` are stable sentinel results.
- This manual should stay aligned with the profile guide classification.
- If cooperative-green gains CPU-parallel behavior later, this spec and guide
  must be updated together.

## TUI Capture

```text
Simple Test Runner v1.0.0-RC
Running: test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl
SimpleOS cooperative green contract PASSED
Files: 1
Passed: 4
Failed: 0
```

## Scenarios

### SimpleOS cooperative green contract

#### queues logical green work without marking it done before the carrier runs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- queues logical green work without marking it done before the carrier runs
- Record the current SimpleOS cooperative carrier queue depth
- Queue a logical green task on the current carrier
- Verify the task is pending until the carrier runs
   - Expected: cooperative_green_ready_count() equals `before + 1`
- Run one cooperative carrier turn
- Verify the queued task completed with its expected value
   - Expected: handle.join() equals `3`
- Verify post-completion join and carrier drain are idempotent
   - Expected: handle.join() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("queues logical green work without marking it done before the carrier runs")
step("Record the current SimpleOS cooperative carrier queue depth")
val before = cooperative_green_ready_count()
step("Queue a logical green task on the current carrier")
val handle = cooperative_green_spawn(simpleos_cooperative_green_value_3)

step("Verify the task is pending until the carrier runs")
expect(handle.is_done()).to_be(false)
expect(cooperative_green_ready_count()).to_equal(before + 1)
step("Run one cooperative carrier turn")
expect(cooperative_green_run_one()).to_be(true)
step("Verify the queued task completed with its expected value")
expect(handle.is_done()).to_be(true)
expect(handle.join()).to_equal(3)
step("Verify post-completion join and carrier drain are idempotent")
expect(handle.join()).to_equal(3)
expect(cooperative_green_run_one()).to_be(false)
```

</details>

#### runs all queued cooperative work on the current carrier

- runs all queued cooperative work on the current carrier
- Record the current SimpleOS cooperative carrier queue depth
- Queue two logical green tasks on the current carrier
- Verify both tasks are visible in the ready queue
   - Expected: cooperative_green_ready_count() equals `before + 2`
- Run the cooperative carrier until the queue is drained
- Verify both queued tasks completed on the current carrier
   - Expected: h1.join() equals `3`
   - Expected: h2.join() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs all queued cooperative work on the current carrier")
step("Record the current SimpleOS cooperative carrier queue depth")
val before = cooperative_green_ready_count()
step("Queue two logical green tasks on the current carrier")
val h1 = cooperative_green_spawn(simpleos_cooperative_green_value_3)
val h2 = cooperative_green_spawn(simpleos_cooperative_green_value_8)

step("Verify both tasks are visible in the ready queue")
expect(cooperative_green_ready_count()).to_equal(before + 2)
step("Run the cooperative carrier until the queue is drained")
val ran = cooperative_green_run_all()

step("Verify both queued tasks completed on the current carrier")
expect(ran).to_be_greater_than(1)
expect(h1.join()).to_equal(3)
expect(h2.join()).to_equal(8)
```

</details>

#### supports direct value scheduling used by profile fanout rows

- supports direct value scheduling used by profile fanout rows
- Record the current SimpleOS cooperative carrier queue depth
- Queue a direct value task on the current carrier
- Verify value work is pending until the carrier runs
   - Expected: cooperative_green_ready_count() equals `before + 1`
- Run one cooperative carrier turn
- Verify the direct value result is returned
   - Expected: handle.join() equals `21`
- Verify post-completion direct value join is idempotent
   - Expected: handle.join() equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports direct value scheduling used by profile fanout rows")
step("Record the current SimpleOS cooperative carrier queue depth")
val before = cooperative_green_ready_count()
step("Queue a direct value task on the current carrier")
val handle = cooperative_green_spawn_value(21)

step("Verify value work is pending until the carrier runs")
expect(handle.is_done()).to_be(false)
expect(cooperative_green_ready_count()).to_equal(before + 1)
step("Run one cooperative carrier turn")
expect(cooperative_green_run_one()).to_be(true)
step("Verify the direct value result is returned")
expect(handle.join()).to_equal(21)
step("Verify post-completion direct value join is idempotent")
expect(handle.join()).to_equal(21)
```

</details>

#### keeps cooperative green out of SimpleOS M:N runtime-pool evidence

- keeps cooperative green out of SimpleOS M:N runtime-pool evidence
- Read the SimpleOS evidence report and multicore-green design
- Verify cooperative green stays classified as current-carrier scheduling
- Reject runtime-pool or Go-like M:N classification for cooperative evidence
   - Expected: absent_in_text(report, "cooperative_green_spawn runtime pool") equals `1`
   - Expected: absent_in_text(report, "cooperative_green_spawn M:N") equals `1`
   - Expected: absent_in_text(profile_index, "cooperative-green runtime-pool") equals `1`
   - Expected: absent_in_text(profile_index, "cooperative-green M:N") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps cooperative green out of SimpleOS M:N runtime-pool evidence")
step("Read the SimpleOS evidence report and multicore-green design")
val report = rt_file_read_text("doc/09_report/simpleos_multicore_green_evidence_2026-06-07.md") ?? ""
val design = rt_file_read_text("doc/05_design/multicore_green.md") ?? ""
val profile_index = rt_file_read_text("doc/09_report/README.md") ?? ""

step("Verify cooperative green stays classified as current-carrier scheduling")
expect(report).to_contain("cooperative current-carrier SimpleOS proof")
expect(design).to_contain("current OS thread")
expect(design).to_contain("not CPU-parallel")
expect(profile_index).to_contain("cooperative-green")
expect(profile_index).to_contain("current OS thread")

step("Reject runtime-pool or Go-like M:N classification for cooperative evidence")
expect(absent_in_text(report, "cooperative_green_spawn runtime pool")).to_equal(1)
expect(absent_in_text(report, "cooperative_green_spawn M:N")).to_equal(1)
expect(absent_in_text(profile_index, "cooperative-green runtime-pool")).to_equal(1)
expect(absent_in_text(profile_index, "cooperative-green M:N")).to_equal(1)
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


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/multicore_green.md`
- **Plan:** `doc/03_plan/sys_test/multicore_green.md`
- **Design:** `doc/04_architecture/runtime/multicore_green.md`
- **Research:** `doc/01_research/local/multicore_green.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `566f043d911a29692e7e1c3828cc09fb11664310c96ff4eec4432c6209a62666`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `566f043d911a29692e7e1c3828cc09fb11664310c96ff4eec4432c6209a62666`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `566f043d911a29692e7e1c3828cc09fb11664310c96ff4eec4432c6209a62666`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl
mirror: doc/06_spec/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'queues logical green work without marking it done before the carrier runs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl:172:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs all queued cooperative work on the current carrier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl:191:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports direct value scheduling used by profile fanout rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
