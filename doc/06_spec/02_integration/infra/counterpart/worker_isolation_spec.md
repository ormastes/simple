# Counterpart Isolated Worker

> Counterpart conformance runs third-party components as differential references.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Counterpart Isolated Worker

Counterpart conformance runs third-party components as differential references.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | In Progress |
| Plan | doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md |
| Design | doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md |
| Source | `test/02_integration/infra/counterpart/worker_isolation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Counterpart conformance runs third-party components as differential references.
Some of those components abort, hang, or produce unbounded output on hostile
input. This feature runs each provider adapter inside `simple-counterpart-worker`,
a separate process that loads exactly one adapter, validates its manifest, reads
length-framed requests, and supervises every invocation under wall-clock, CPU,
memory and output-size budgets. Spec authors get a typed receipt instead of a
dead test process.

## Scope and Preconditions

The scenarios build two C artifacts from the repository — the worker
(`src/runtime/counterpart_worker_runtime.c`) and the mock provider adapter
(`tools/counterpart/adapters/mock/simple_counterpart_mock.c`) — with a host
`cc`, into `build/counterpart/`. The mock adapter publishes `mock.echo`,
`mock.hash`, `mock.error` and `mock.crash`; `mock.crash` calls `abort()` by
contract, which is exactly the condition these scenarios must survive.

## Primary Workflow

The provider writes one length-framed request to a file, spawns the worker with
that file on stdin, and reads back one framed SDN receipt. The receipt's
`provider_status` is mapped onto the frozen vocabulary in
`src/lib/common/spec/evidence/counterpart/model.spl` without normalization:

| Receipt | provider_status | comparison_status | artifact_status |
|---|---|---|---|
| adapter returned | executed | not_compared | complete |
| adapter aborted | crashed | failed | partial |
| budget exceeded | timed_out | failed | partial |
| adapter absent | unavailable | not_compared | absent |
| bad manifest | rejected_manifest | failed | absent |

## Key Concepts

| Concept | Description |
|---------|-------------|
| Length framing | `SCFQ1 <component_len> <request_len>` header, then raw payload bytes |
| Parent-side receipt | The worker's supervising parent, not the crashing child, writes the receipt |
| Budget kill | A wall-clock or output-size kill is `timed_out`, never a silent pass |
| Containment | A crashed provider leaves the worker's exit code at 0 and the spec process alive |

## Related Specifications

- [Counterpart evidence model](../../../../src/lib/common/spec/evidence/counterpart/model.spl) — frozen ProviderStatus vocabulary

## Evidence and Provenance

Evidence is the worker's own framed receipt, produced by the parent process
after `waitpid` reports how the child ended. Signal 6 (`SIGABRT`) from
`mock.crash` and signal 9 (`SIGKILL`) from a budget kill are observed values,
not assumed ones.

## Recovery and Troubleshooting

If a scenario reports `unavailable`, the adapter or worker binary failed to
build or load — check the compile step's output first. A `crashed` result from
`mock.echo` would mean the worker itself is faulty, not the adapter.

## Compatibility and Limitations

POSIX only: the worker uses `fork`, `poll`, `setrlimit` and `waitpid`. The
in-process provider path is deliberately not exercised here — the
`rt_counterpart_*` shim is not yet linked into the runtime
(doc/08_tracking/bug/counterpart_abi_shim_not_linked_into_runtime_2026-08-09.md),
and this lane's isolation guarantees must not depend on it.

## Scenarios

### Counterpart Isolated Worker

#### reports a normal invocation as executed with a real response

- builds the worker and the mock adapter
- Compile the worker and the mock provider adapter with the host cc
- Verify both artifacts compiled without error
   - Expected: code equals `0`
- reports a normal invocation as executed with a real response
- Invoke mock.echo through the isolated worker
- Verify the provider status is executed
   - Expected: provider_status_name(outcome.provider_status) equals `executed`
- Verify the adapter response came back through the worker
- Verify the invocation is treated as a pass
   - Expected: outcome_is_pass(outcome) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("builds the worker and the mock adapter")
step("Compile the worker and the mock provider adapter with the host cc")
val code = build_worker_and_adapter()
step("Verify both artifacts compiled without error")
expect(code).to_equal(0)

# @req REQ-SSPEC-INTEGRATION
step("reports a normal invocation as executed with a real response")
step("Invoke mock.echo through the isolated worker")
val outcome = invoke_or_fail(default_config(), "mock.echo", "hello-counterpart")
step("Verify the provider status is executed")
expect(provider_status_name(outcome.provider_status)).to_equal("executed")
step("Verify the adapter response came back through the worker")
expect(outcome.response).to_contain("mock.echo_response@1")
expect(outcome.response).to_contain("hello-counterpart")
step("Verify the invocation is treated as a pass")
expect(outcome_is_pass(outcome)).to_equal(true)
```

</details>

#### reports an aborting provider as crashed while the spec process survives

- builds the worker and the mock adapter
- Compile the worker and the mock provider adapter with the host cc
- Verify both artifacts compiled without error
   - Expected: code equals `0`
- reports an aborting provider as crashed while the spec process survives
- Invoke mock.crash, which aborts by contract, through the isolated worker
- Verify the provider status is crashed
   - Expected: provider_status_name(outcome.provider_status) equals `crashed`
- Verify the child was observed dying on SIGABRT
   - Expected: outcome.exit_signal equals `6`
- Verify the crash is a failed comparison over a partial artifact
   - Expected: outcome.comparison_status equals `failed`
   - Expected: outcome.artifact_status equals `partial`
- Verify the worker itself contained the crash and exited cleanly
   - Expected: outcome.worker_exit_code equals `0`
- Verify this spec process is still alive by invoking again
   - Expected: provider_status_name(after.provider_status) equals `executed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("builds the worker and the mock adapter")
step("Compile the worker and the mock provider adapter with the host cc")
val code = build_worker_and_adapter()
step("Verify both artifacts compiled without error")
expect(code).to_equal(0)

# @req REQ-SSPEC-INTEGRATION
step("reports an aborting provider as crashed while the spec process survives")
step("Invoke mock.crash, which aborts by contract, through the isolated worker")
val outcome = invoke_or_fail(default_config(), "mock.crash", "boom")
step("Verify the provider status is crashed")
expect(provider_status_name(outcome.provider_status)).to_equal("crashed")
step("Verify the child was observed dying on SIGABRT")
expect(outcome.exit_signal).to_equal(6)
step("Verify the crash is a failed comparison over a partial artifact")
expect(outcome.comparison_status).to_equal("failed")
expect(outcome.artifact_status).to_equal("partial")
step("Verify the worker itself contained the crash and exited cleanly")
expect(outcome.worker_exit_code).to_equal(0)
step("Verify this spec process is still alive by invoking again")
val after = invoke_or_fail(default_config(), "mock.echo", "still-alive")
expect(provider_status_name(after.provider_status)).to_equal("executed")
```

</details>

#### reports a hung provider as timed_out instead of hanging forever

- builds the worker and the mock adapter
- Compile the worker and the mock provider adapter with the host cc
- Verify both artifacts compiled without error
   - Expected: code equals `0`
- reports a hung provider as timed_out instead of hanging forever
- Invoke mock.echo with a 200 ms budget against a 3000 ms stall
- Verify the provider status is timed_out
   - Expected: provider_status_name(outcome.provider_status) equals `timed_out`
- Verify the deadline was enforced by killing the child
   - Expected: outcome.exit_signal equals `9`
- Verify the timeout is a failed comparison over a partial artifact
   - Expected: outcome.comparison_status equals `failed`
   - Expected: outcome.artifact_status equals `partial`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("builds the worker and the mock adapter")
step("Compile the worker and the mock provider adapter with the host cc")
val code = build_worker_and_adapter()
step("Verify both artifacts compiled without error")
expect(code).to_equal(0)

# @req REQ-SSPEC-INTEGRATION
step("reports a hung provider as timed_out instead of hanging forever")
step("Invoke mock.echo with a 200 ms budget against a 3000 ms stall")
val outcome = invoke_or_fail(config_with_timeout(200, 3000), "mock.echo", "stalled")
step("Verify the provider status is timed_out")
expect(provider_status_name(outcome.provider_status)).to_equal("timed_out")
step("Verify the deadline was enforced by killing the child")
expect(outcome.exit_signal).to_equal(9)
expect(outcome.diagnostic).to_contain("wall-clock budget")
step("Verify the timeout is a failed comparison over a partial artifact")
expect(outcome.comparison_status).to_equal("failed")
expect(outcome.artifact_status).to_equal("partial")
```

</details>

#### reports an oversized response as timed_out rather than a truncated pass

- builds the worker and the mock adapter
- Compile the worker and the mock provider adapter with the host cc
- Verify both artifacts compiled without error
   - Expected: code equals `0`
- reports an oversized response as timed_out rather than a truncated pass
- Ask mock.echo to echo 200000 bytes under a 4096 byte output budget
- Verify the provider status is timed_out
   - Expected: provider_status_name(outcome.provider_status) equals `timed_out`
- Verify the output budget is named in the diagnostic
- Verify no partial response is presented as a result
   - Expected: outcome.response equals ``
   - Expected: outcome_is_pass(outcome) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("builds the worker and the mock adapter")
step("Compile the worker and the mock provider adapter with the host cc")
val code = build_worker_and_adapter()
step("Verify both artifacts compiled without error")
expect(code).to_equal(0)

# @req REQ-SSPEC-INTEGRATION
step("reports an oversized response as timed_out rather than a truncated pass")
step("Ask mock.echo to echo 200000 bytes under a 4096 byte output budget")
val payload = large_ascii_payload(200000)
val outcome = invoke_or_fail(config_with_output_budget(4096), "mock.echo", payload)
step("Verify the provider status is timed_out")
expect(provider_status_name(outcome.provider_status)).to_equal("timed_out")
step("Verify the output budget is named in the diagnostic")
expect(outcome.diagnostic).to_contain("output budget")
step("Verify no partial response is presented as a result")
expect(outcome.response).to_equal("")
expect(outcome_is_pass(outcome)).to_equal(false)
```

</details>

### Counterpart Isolated Worker Status Vocabulary

#### never reports a crash as unavailable or as a pass

- builds the worker and the mock adapter
- Compile the worker and the mock provider adapter with the host cc
- Verify both artifacts compiled without error
   - Expected: code equals `0`
- never reports a crash as unavailable or as a pass
- Invoke the aborting component
- Verify crashed is kept distinct from unavailable
   - Expected: provider_status_name(outcome.provider_status) equals `crashed`
- Verify the crash is not counted as a pass
   - Expected: outcome_is_pass(outcome) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("builds the worker and the mock adapter")
step("Compile the worker and the mock provider adapter with the host cc")
val code = build_worker_and_adapter()
step("Verify both artifacts compiled without error")
expect(code).to_equal(0)

# @req REQ-SSPEC-INTEGRATION
step("never reports a crash as unavailable or as a pass")
step("Invoke the aborting component")
val outcome = invoke_or_fail(default_config(), "mock.crash", "boom")
step("Verify crashed is kept distinct from unavailable")
expect(provider_status_name(outcome.provider_status)).to_not_equal("unavailable")
expect(provider_status_name(outcome.provider_status)).to_equal("crashed")
step("Verify the crash is not counted as a pass")
expect(outcome_is_pass(outcome)).to_equal(false)
```

</details>

#### reports a missing adapter as unavailable, not as crashed

- reports a missing adapter as unavailable, not as crashed
- Point the worker at an adapter library that does not exist
- Verify a missing adapter is an environment fact, not a defect
   - Expected: provider_status_name(outcome.provider_status) equals `unavailable`
   - Expected: outcome.artifact_status equals `absent`
   - Expected: outcome_is_pass(outcome) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports a missing adapter as unavailable, not as crashed")
step("Point the worker at an adapter library that does not exist")
var config = default_config()
config.adapter_path = "build/counterpart/libsimple_counterpart_absent.so"
val outcome = invoke_or_fail(config, "mock.echo", "hello")
step("Verify a missing adapter is an environment fact, not a defect")
expect(provider_status_name(outcome.provider_status)).to_equal("unavailable")
expect(outcome.artifact_status).to_equal("absent")
expect(outcome_is_pass(outcome)).to_equal(false)
```

</details>

#### frames a request with explicit ASCII decimal lengths

- frames a request with explicit ASCII decimal lengths
- Frame a request for mock.echo
- Verify the frame header carries both payload lengths


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("frames a request with explicit ASCII decimal lengths")
step("Frame a request for mock.echo")
match frame_request("mock.echo", "hello"):
    Ok(frame):
        step("Verify the frame header carries both payload lengths")
        expect(frame).to_contain("SCFQ1 9 5\n")
        expect(frame).to_contain("mock.echohello")
    Err(message):
        fail("framing failed: {message}")
```

</details>

#### refuses stdout that carries no receipt frame

- refuses stdout that carries no receipt frame
- Parse worker stdout that produced no framed receipt
- Verify the missing frame is an error, not an assumed unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses stdout that carries no receipt frame")
step("Parse worker stdout that produced no framed receipt")
match parse_receipt("cc: command not found\n"):
    Ok(_outcome):
        fail("unframed stdout must not parse into a provider status")
    Err(message):
        step("Verify the missing frame is an error, not an assumed unavailable")
        expect(message).to_contain("SCFR1")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md`
- **Design:** `doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3034d98de0bf3fc2227100a625f7398f21ab081d0dc342a694c7f164f3b0c1f8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3034d98de0bf3fc2227100a625f7398f21ab081d0dc342a694c7f164f3b0c1f8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3034d98de0bf3fc2227100a625f7398f21ab081d0dc342a694c7f164f3b0c1f8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/infra/counterpart/worker_isolation_spec.spl
mirror: doc/06_spec/02_integration/infra/counterpart/worker_isolation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/infra/counterpart/worker_isolation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/02_integration/infra/counterpart/worker_isolation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/infra/counterpart/worker_isolation_spec.spl:171:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds the worker and the mock adapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/infra/counterpart/worker_isolation_spec.spl:180:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a normal invocation as executed with a real response' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/infra/counterpart/worker_isolation_spec.spl:194:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports an aborting provider as crashed while the spec process survives' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
