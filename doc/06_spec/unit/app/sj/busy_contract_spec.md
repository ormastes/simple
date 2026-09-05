# BUSY Contract Specification

> As a caller of the `sj` daemon, when a lease cannot be acquired I need a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BUSY Contract Specification

As a caller of the `sj` daemon, when a lease cannot be acquired I need a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/sj/busy_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

As a caller of the `sj` daemon, when a lease cannot be acquired I need a
BUSY refusal that is unmistakable: `exit_code` 75 (EX_TEMPFAIL), a non-empty
stderr naming the blocking lease and holder pid, and a JSON wire response that
carries both. A successful command must carry exit 0 and no BUSY text.

This spec exercises the REAL product path — `std.service.lease_manager` for the
BUSY message and `app.sj_daemon.request_handler` for the exit code and wire
format. It previously declared its own copy of `LeaseManager` and its own
`format_busy_json` (a function that does not exist in `src/`), so it proved
nothing about the product.

## Scenarios

### BUSY Contract - Refusal Signal

#### BUSY result indicates failure

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- BUSY result indicates failure
   - Expected: first.ok is true
   - Expected: second.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BUSY result indicates failure")
var mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_exclusive(mgr, pid, 30000i64)
val second = try_acquire_exclusive(mgr, pid, 30000i64)
expect(first.ok).to_equal(true)
expect(second.ok).to_equal(false)
val msg = second.busy_message
expect(msg).to_contain("BUSY")
```

</details>

#### BUSY message is not empty

- BUSY message is not empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BUSY message is not empty")
var mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_exclusive(mgr, pid, 30000i64)
val second = try_acquire_exclusive(mgr, pid, 30000i64)
val msg = second.busy_message
expect(msg.len()).to_be_greater_than(0i64)
```

</details>

#### BUSY message names the blocking lease id and holder pid

- BUSY message names the blocking lease id and holder pid


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BUSY message names the blocking lease id and holder pid")
var mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_exclusive(mgr, pid, 30000i64)
val second = try_acquire_exclusive(mgr, pid, 30000i64)
val msg = second.busy_message
val fid = first.lease_id
expect(msg).to_contain(fid)
expect(msg).to_contain("pid")
```

</details>

### BUSY Contract - Exit Code 75

#### refuses a mutating command with exit 75 while an exclusive lease is held

- refuses a mutating command with exit 75 while an exclusive lease is held
   - Expected: held.ok is true
   - Expected: resp.exit_code equals `75i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a mutating command with exit 75 while an exclusive lease is held")
var handler = sj_request_handler_new(".", 30000i64)
val pid = rt_getpid()
val held = try_acquire_exclusive(handler.lease_manager, pid, 30000i64)
expect(held.ok).to_equal(true)
val resp = handle_cli_args(handler, ["commit", "-m", "x"], pid)
expect(resp.exit_code).to_equal(75i64)
expect(resp.stderr).to_contain("BUSY")
```

</details>

### BUSY Contract - JSON Wire Format

#### serializes the BUSY refusal with exit code and stderr

- serializes the BUSY refusal with exit code and stderr


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes the BUSY refusal with exit code and stderr")
var mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_exclusive(mgr, pid, 30000i64)
val second = try_acquire_exclusive(mgr, pid, 30000i64)
val resp = CommandResponse(
    exit_code: 75i64,
    stdout: "",
    stderr: second.busy_message,
    classification: "mutating",
    lease_kind: LEASE_EXCLUSIVE
)
val json = response_json(resp)
expect(json).to_contain("\"exit_code\":75")
expect(json).to_contain("BUSY")
expect(json).to_contain("\"classification\":\"mutating\"")
```

</details>

### BUSY Contract - Exit 0 Regression

#### successful lease does not produce BUSY

- successful lease does not produce BUSY
   - Expected: result.ok is true
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("successful lease does not produce BUSY")
var mgr = lease_manager_new()
val pid = rt_getpid()
val result = try_acquire_exclusive(mgr, pid, 30000i64)
expect(result.ok).to_equal(true)
val msg = result.busy_message
expect(msg).to_equal("")
```

</details>

#### released lease allows next acquire

- released lease allows next acquire
   - Expected: released is true
   - Expected: second.ok is true
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("released lease allows next acquire")
var mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_exclusive(mgr, pid, 30000i64)
val released = release_lease(mgr, first.lease_id)
expect(released).to_equal(true)
val second = try_acquire_exclusive(mgr, pid, 30000i64)
expect(second.ok).to_equal(true)
val msg = second.busy_message
expect(msg).to_equal("")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `44014b9fd5d4c527ab999000ce8cc68b24f837ac395f45d2c7cb8deae3f518d1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `44014b9fd5d4c527ab999000ce8cc68b24f837ac395f45d2c7cb8deae3f518d1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `44014b9fd5d4c527ab999000ce8cc68b24f837ac395f45d2c7cb8deae3f518d1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/sj/busy_contract_spec.spl
mirror: doc/06_spec/unit/app/sj/busy_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/sj/busy_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/sj/busy_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/sj/busy_contract_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BUSY result indicates failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sj/busy_contract_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BUSY message is not empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sj/busy_contract_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BUSY message names the blocking lease id and holder pid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
