# Wine Nt Thread Wait Specification

> Tests covering Wine NT thread/wait bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Nt Thread Wait Specification

## Scenarios

### Wine NT thread/wait bridge

#### lists the modeled CreateThread, WaitForSingleObject, and GetLastError calls

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lists the modeled CreateThread, WaitForSingleObject, and GetLastError calls
   - Expected: calls.len() equals `3`
   - Expected: calls[0] equals `CreateThread`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lists the modeled CreateThread, WaitForSingleObject, and GetLastError calls")
val calls = wine_nt_thread_wait_required_calls()
expect(calls.len()).to_equal(3)
expect(calls[0]).to_equal("CreateThread")
```

</details>

#### blocks thread table readiness until thread prerequisites pass

- blocks thread table readiness until thread prerequisites pass
   - Expected: table.ready is false
   - Expected: table.state equals `missing-api-thread-detach`
   - Expected: wine_nt_get_last_error(table) equals `missing-api-thread-detach`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("blocks thread table readiness until thread prerequisites pass")
val table = wine_nt_thread_table_new("thread-create thread-join")
expect(table.ready).to_equal(false)
expect(table.state).to_equal("missing-api-thread-detach")
expect(wine_nt_get_last_error(table)).to_equal("missing-api-thread-detach")
```

</details>

#### creates a modeled thread handle and waits for completion

- creates a modeled thread handle and waits for completion
   - Expected: created.ok is true
   - Expected: created.handle equals `0x80`
   - Expected: waited.ok is true
   - Expected: waited.wait_status equals `WAIT_OBJECT_0`
   - Expected: waited.exit_code equals `7`
   - Expected: wine_nt_get_last_error(waited.table) equals `OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates a modeled thread handle and waits for completion")
val created = wine_nt_create_thread(wine_nt_thread_table_new(_all_thread_apis()), "main", 7)
expect(created.ok).to_equal(true)
expect(created.handle).to_equal(0x80)
val waited = wine_nt_wait_for_single_object(created.table, created.handle, 1000)
expect(waited.ok).to_equal(true)
expect(waited.wait_status).to_equal("WAIT_OBJECT_0")
expect(waited.exit_code).to_equal(7)
expect(wine_nt_get_last_error(waited.table)).to_equal("OK")
```

</details>

#### rejects invalid entrypoints and exposes last error

- rejects invalid entrypoints and exposes last error
   - Expected: created.ok is false
   - Expected: created.state equals `invalid-entrypoint`
   - Expected: wine_nt_get_last_error(created.table) equals `ERROR_INVALID_PARAMETER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid entrypoints and exposes last error")
val created = wine_nt_create_thread(wine_nt_thread_table_new(_all_thread_apis()), "", 0)
expect(created.ok).to_equal(false)
expect(created.state).to_equal("invalid-entrypoint")
expect(wine_nt_get_last_error(created.table)).to_equal("ERROR_INVALID_PARAMETER")
```

</details>

#### rejects invalid wait handles and exposes last error

- rejects invalid wait handles and exposes last error
   - Expected: waited.ok is false
   - Expected: waited.state equals `invalid-handle`
   - Expected: wine_nt_get_last_error(waited.table) equals `ERROR_INVALID_HANDLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid wait handles and exposes last error")
val waited = wine_nt_wait_for_single_object(wine_nt_thread_table_new(_all_thread_apis()), 0x99, 0)
expect(waited.ok).to_equal(false)
expect(waited.state).to_equal("invalid-handle")
expect(wine_nt_get_last_error(waited.table)).to_equal("ERROR_INVALID_HANDLE")
```

</details>

#### reports timeout for unsignaled modeled handles

- reports timeout for unsignaled modeled handles
   - Expected: created.state equals `created-pending`
   - Expected: waited.ok is true
   - Expected: waited.state equals `wait-timeout`
   - Expected: waited.wait_status equals `WAIT_TIMEOUT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports timeout for unsignaled modeled handles")
val created = wine_nt_create_pending_thread(wine_nt_thread_table_new(_all_thread_apis()), "worker")
expect(created.state).to_equal("created-pending")
val waited = wine_nt_wait_for_single_object(created.table, created.handle, 0)
expect(waited.ok).to_equal(true)
expect(waited.state).to_equal("wait-timeout")
expect(waited.wait_status).to_equal("WAIT_TIMEOUT")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_nt_thread_wait_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine NT thread/wait bridge.
- Wine NT thread/wait bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `8dbb54411c235b9ed6171a952c467f866d05b0cb96fb06b1f0c855cf32d62fa0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8dbb54411c235b9ed6171a952c467f866d05b0cb96fb06b1f0c855cf32d62fa0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8dbb54411c235b9ed6171a952c467f866d05b0cb96fb06b1f0c855cf32d62fa0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/wine_nt_thread_wait_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_nt_thread_wait_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_nt_thread_wait_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_nt_thread_wait_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_nt_thread_wait_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_nt_thread_wait_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists the modeled CreateThread, WaitForSingleObject, and GetLastError calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_nt_thread_wait_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks thread table readiness until thread prerequisites pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_nt_thread_wait_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a modeled thread handle and waits for completion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
