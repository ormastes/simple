# sj daemon mutual exclusion — the BUSY / exit_code 75 branch must be REACHABLE

> This defect class is invisible to positive/presence assertions: "a lease was

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sj daemon mutual exclusion — the BUSY / exit_code 75 branch must be REACHABLE

This defect class is invisible to positive/presence assertions: "a lease was

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/sj_daemon_mutual_exclusion_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Why every example here carries a NEGATIVE control

This defect class is invisible to positive/presence assertions: "a lease was
granted", "a response came back", "the exit code is an integer" all pass just
as happily against the broken code. Only a paired
`must-be-75` / `must-NOT-be-75` observation can tell the two worlds apart, so
each example asserts BOTH the refusal and the corresponding grant.

## Scenarios

### sj daemon - mutual exclusion is real (exit_code 75 reachable)

#### refuses a second concurrent write request with exit_code 75

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- refuses a second concurrent write request with exit_code 75
   - Expected: held.ok is true
   - Expected: active_lease_count(handler.lease_manager) equals `1i64`
   - Expected: second.exit_code equals `75i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses a second concurrent write request with exit_code 75")
val pid = rt_getpid()
val handler = sj_request_handler_new(".", 60000i64)
# Request #1 takes the exclusive lease and is still holding it.
val held = try_acquire_exclusive(handler.lease_manager, pid, 60000i64)
expect(held.ok).to_equal(true)
# The handler must SEE that lease. Before the fix this was 0.
expect(active_lease_count(handler.lease_manager)).to_equal(1i64)
# Request #2 arrives while #1 holds the lease.
val second = handle_cli_args(handler, ["sj", "commit", "-m", "x"], pid)
expect(second.exit_code).to_equal(75i64)
expect(second.stderr).to_contain("BUSY")
```

</details>

#### NEGATIVE CONTROL: the same request with no lease held is NOT 75

- NEGATIVE CONTROL: the same request with no lease held is NOT 75
   - Expected: active_lease_count(handler.lease_manager) equals `0i64`
   - Expected: only.exit_code == 75i64 is false
   - Expected: only.exit_code equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NEGATIVE CONTROL: the same request with no lease held is NOT 75")
# Without this, the example above would be satisfied by a handler that
# returned 75 unconditionally.
val pid = rt_getpid()
val handler = sj_request_handler_new(".", 60000i64)
expect(active_lease_count(handler.lease_manager)).to_equal(0i64)
val only = handle_cli_args(handler, ["sj", "commit", "-m", "x"], pid)
expect(only.exit_code == 75i64).to_equal(false)
expect(only.exit_code).to_equal(0i64)
```

</details>

#### releases the lease at the end of a request so the next one succeeds

- releases the lease at the end of a request so the next one succeeds
   - Expected: first.exit_code equals `0i64`
   - Expected: active_lease_count(handler.lease_manager) equals `0i64`
   - Expected: second.exit_code equals `0i64`
   - Expected: second.exit_code == 75i64 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("releases the lease at the end of a request so the next one succeeds")
val pid = rt_getpid()
val handler = sj_request_handler_new(".", 60000i64)
val first = handle_cli_args(handler, ["sj", "commit", "-m", "a"], pid)
expect(first.exit_code).to_equal(0i64)
# ABSENCE CONTROL: no lease may survive a completed request.
expect(active_lease_count(handler.lease_manager)).to_equal(0i64)
val second = handle_cli_args(handler, ["sj", "commit", "-m", "b"], pid)
expect(second.exit_code).to_equal(0i64)
expect(second.exit_code == 75i64).to_equal(false)
```

</details>

### sj daemon - exclusion survives the by-value SjClient caller chain

#### sees the lease through SjClient -> fallback_exec -> handle_cli_args

- sees the lease through SjClient -> fallback_exec -> handle_cli_args
   - Expected: held.ok is true
   - Expected: resp.exit_code equals `75i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sees the lease through SjClient -> fallback_exec -> handle_cli_args")
val pid = rt_getpid()
val client = sj_client_new(".", 60000i64)
val held = try_acquire_exclusive(client.handler.lease_manager, pid, 60000i64)
expect(held.ok).to_equal(true)
val resp = fallback_exec(client.handler, ["sj", "commit", "-m", "x"], pid)
expect(resp.exit_code).to_equal(75i64)
```

</details>

#### NEGATIVE CONTROL: same chain with no lease held is NOT 75

- NEGATIVE CONTROL: same chain with no lease held is NOT 75
   - Expected: resp.exit_code == 75i64 is false
   - Expected: resp.exit_code equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NEGATIVE CONTROL: same chain with no lease held is NOT 75")
val pid = rt_getpid()
val client = sj_client_new(".", 60000i64)
val resp = fallback_exec(client.handler, ["sj", "commit", "-m", "x"], pid)
expect(resp.exit_code == 75i64).to_equal(false)
expect(resp.exit_code).to_equal(0i64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `45cb99bb5292abe011e294c0bfbc373e9401eb274d58a6d7bb8c8f0ae0f10def`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `45cb99bb5292abe011e294c0bfbc373e9401eb274d58a6d7bb8c8f0ae0f10def`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `45cb99bb5292abe011e294c0bfbc373e9401eb274d58a6d7bb8c8f0ae0f10def`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/sj_daemon_mutual_exclusion_spec.spl
mirror: doc/06_spec/integration/app/sj_daemon_mutual_exclusion_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/sj_daemon_mutual_exclusion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/sj_daemon_mutual_exclusion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/sj_daemon_mutual_exclusion_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a second concurrent write request with exit_code 75' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/sj_daemon_mutual_exclusion_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'NEGATIVE CONTROL: the same request with no lease held is NOT 75' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/sj_daemon_mutual_exclusion_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'releases the lease at the end of a request so the next one succeeds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
