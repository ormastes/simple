# Async Process Specification

> Native SimpleOS process control is async-first. POSIX process wrappers block

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Process Specification

Native SimpleOS process control is async-first. POSIX process wrappers block

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/posix/process_async_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Native SimpleOS process control is async-first. POSIX process wrappers block
over this request facade.

## Scenarios

### process_async request lifecycle

#### completes invalid spawn paths without entering the syscall backend

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- completes invalid spawn paths without entering the syscall backend
   - Expected: process_async_is_complete(req) is true
   - Expected: process_async_result(req) equals `0 - EINVAL as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("completes invalid spawn paths without entering the syscall backend")
process_async_init()
val req = process_async_spawn("", [], 2)

expect(req).to_be_less_than(PROCESS_MAX_REQUESTS)
expect(process_async_is_complete(req)).to_equal(true)
expect(process_async_result(req)).to_equal(0 - EINVAL as i64)

process_async_free_request(req)
```

</details>

#### completes invalid exec paths without entering the syscall backend

- completes invalid exec paths without entering the syscall backend
   - Expected: process_async_is_complete(req) is true
   - Expected: process_async_result(req) equals `0 - EINVAL as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("completes invalid exec paths without entering the syscall backend")
process_async_init()
val req = process_async_execve("", [], [])

expect(req).to_be_less_than(PROCESS_MAX_REQUESTS)
expect(process_async_is_complete(req)).to_equal(true)
expect(process_async_result(req)).to_equal(0 - EINVAL as i64)

process_async_free_request(req)
```

</details>

#### completes invalid signal requests without entering the syscall backend

- completes invalid signal requests without entering the syscall backend
   - Expected: process_async_is_complete(req) is true
   - Expected: process_async_result(req) equals `0 - EINVAL as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("completes invalid signal requests without entering the syscall backend")
process_async_init()
val req = process_async_signal(42u64, -1)

expect(req).to_be_less_than(PROCESS_MAX_REQUESTS)
expect(process_async_is_complete(req)).to_equal(true)
expect(process_async_result(req)).to_equal(0 - EINVAL as i64)

process_async_free_request(req)
```

</details>

#### reports EIO for invalid request handles

- reports EIO for invalid request handles
   - Expected: process_async_is_complete(PROCESS_MAX_REQUESTS) is true
   - Expected: process_async_result(PROCESS_MAX_REQUESTS) equals `0 - EIO as i64`
   - Expected: process_wait_request(PROCESS_MAX_REQUESTS) equals `0 - EIO as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports EIO for invalid request handles")
expect(process_async_is_complete(PROCESS_MAX_REQUESTS)).to_equal(true)
expect(process_async_result(PROCESS_MAX_REQUESTS)).to_equal(0 - EIO as i64)
expect(process_wait_request(PROCESS_MAX_REQUESTS)).to_equal(0 - EIO as i64)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5118d037e1b502dd011700fce083c951ddb85c97842c2b6bf42f994c514d89db`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5118d037e1b502dd011700fce083c951ddb85c97842c2b6bf42f994c514d89db`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5118d037e1b502dd011700fce083c951ddb85c97842c2b6bf42f994c514d89db`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/posix/process_async_spec.spl
mirror: doc/06_spec/unit/os/posix/process_async_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/posix/process_async_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/posix/process_async_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/posix/process_async_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'completes invalid spawn paths without entering the syscall backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/posix/process_async_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'completes invalid exec paths without entering the syscall backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/posix/process_async_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'completes invalid signal requests without entering the syscall backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
