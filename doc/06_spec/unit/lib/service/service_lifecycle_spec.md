# Service Lifecycle Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Service Lifecycle Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/service/service_lifecycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### Service Lifecycle - PID File

#### acquires PID file on first attempt

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- acquires PID file on first attempt
   - Expected: state.acquired is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("acquires PID file on first attempt")
val path = "/tmp/sj-test-lifecycle-{rt_time_now_unix_micros()}.pid"
val state = acquire_pid_file(path)
expect(state.acquired).to_equal(true)
expect(state.pid).to_be_greater_than(0i64)
# Cleanup
release_pid_file(state)
```

</details>

#### writes current PID to file

- writes current PID to file
   - Expected: written_pid equals `rt_getpid()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes current PID to file")
val path = "/tmp/sj-test-lifecycle-pid-{rt_time_now_unix_micros()}.pid"
val state = acquire_pid_file(path)
val written_pid = read_pid_file(path)
expect(written_pid).to_equal(rt_getpid())
release_pid_file(state)
```

</details>

#### rejects second acquisition while first is alive

- rejects second acquisition while first is alive
   - Expected: first.acquired is true
   - Expected: second.acquired is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects second acquisition while first is alive")
val path = "/tmp/sj-test-lifecycle-dup-{rt_time_now_unix_micros()}.pid"
val first = acquire_pid_file(path)
val second = acquire_pid_file(path)
expect(first.acquired).to_equal(true)
expect(second.acquired).to_equal(false)
release_pid_file(first)
```

</details>

#### releases PID file and allows re-acquisition

- releases PID file and allows re-acquisition
   - Expected: second.acquired is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("releases PID file and allows re-acquisition")
val path = "/tmp/sj-test-lifecycle-reacq-{rt_time_now_unix_micros()}.pid"
val first = acquire_pid_file(path)
release_pid_file(first)
val second = acquire_pid_file(path)
expect(second.acquired).to_equal(true)
release_pid_file(second)
```

</details>

#### PID file does not exist after release

- PID file does not exist after release
   - Expected: rt_file_exists(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PID file does not exist after release")
val path = "/tmp/sj-test-lifecycle-cleanup-{rt_time_now_unix_micros()}.pid"
val state = acquire_pid_file(path)
release_pid_file(state)
expect(rt_file_exists(path)).to_equal(false)
```

</details>

### Service Lifecycle - Liveness Check

#### reports alive for current process PID file

- reports alive for current process PID file
   - Expected: is_daemon_alive(path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports alive for current process PID file")
val path = "/tmp/sj-test-alive-{rt_time_now_unix_micros()}.pid"
val state = acquire_pid_file(path)
expect(is_daemon_alive(path)).to_equal(true)
release_pid_file(state)
```

</details>

#### reports not alive for missing PID file

- reports not alive for missing PID file
   - Expected: is_daemon_alive(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports not alive for missing PID file")
val path = "/tmp/sj-test-nofile-{rt_time_now_unix_micros()}.pid"
expect(is_daemon_alive(path)).to_equal(false)
```

</details>

#### reports not alive for stale PID file

- reports not alive for stale PID file
   - Expected: is_daemon_alive(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports not alive for stale PID file")
val path = "/tmp/sj-test-stale-{rt_time_now_unix_micros()}.pid"
# Write a PID that definitely does not exist (99999999)
rt_file_write_text(path, "99999999\n0")
expect(is_daemon_alive(path)).to_equal(false)
rt_file_delete(path)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `d12329d6235dc9ea5296b8856d79aa4bda3ece4575838df01471c91ceeebb409`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d12329d6235dc9ea5296b8856d79aa4bda3ece4575838df01471c91ceeebb409`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d12329d6235dc9ea5296b8856d79aa4bda3ece4575838df01471c91ceeebb409`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/service/service_lifecycle_spec.spl
mirror: doc/06_spec/unit/lib/service/service_lifecycle_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/service/service_lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/service/service_lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/service/service_lifecycle_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'acquires PID file on first attempt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/service/service_lifecycle_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes current PID to file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/service/service_lifecycle_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects second acquisition while first is alive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
