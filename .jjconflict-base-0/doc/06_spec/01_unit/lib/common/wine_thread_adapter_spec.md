# Wine Thread Adapter Specification

> Tests covering Wine thread adapter contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Thread Adapter Specification

## Scenarios

### Wine thread adapter contract

#### lists pthread, TLS, synchronization, wait-object, and fault APIs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lists pthread, TLS, synchronization, wait-object, and fault APIs
   - Expected: apis[0] equals `thread-create`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists pthread, TLS, synchronization, wait-object, and fault APIs")
val apis = wine_thread_adapter_required_apis()
expect(apis.len()).to_be_greater_than(20)
expect(apis[0]).to_equal("thread-create")
```

</details>

#### reports the first missing thread adapter API

- reports the first missing thread adapter API
   - Expected: missing[0] equals `thread-detach`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the first missing thread adapter API")
val missing = wine_thread_adapter_missing_apis("thread-create thread-join")
expect(missing[0]).to_equal("thread-detach")
```

</details>

#### maps currently available thread SFFI calls to their runtime symbols

- maps currently available thread SFFI calls to their runtime symbols
   - Expected: wine_thread_adapter_sffi_binding("thread-create") equals `spl_thread_create`
   - Expected: wine_thread_adapter_sffi_binding("mutex-try-lock") equals `spl_mutex_try_lock`
   - Expected: wine_thread_adapter_sffi_binding("condvar-wait-timeout") equals `spl_condvar_wait_timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps currently available thread SFFI calls to their runtime symbols")
expect(wine_thread_adapter_sffi_binding("thread-create")).to_equal("spl_thread_create")
expect(wine_thread_adapter_sffi_binding("mutex-try-lock")).to_equal("spl_mutex_try_lock")
expect(wine_thread_adapter_sffi_binding("condvar-wait-timeout")).to_equal("spl_condvar_wait_timeout")
```

</details>

#### shows existing thread SFFI still lacks Wine TLS and wait objects

- shows existing thread SFFI still lacks Wine TLS and wait objects
   - Expected: result.ready is false
   - Expected: result.state equals `missing-api-tls-key-create`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows existing thread SFFI still lacks Wine TLS and wait objects")
val result = wine_thread_adapter_gate(_existing_thread_sffi_apis())
expect(result.ready).to_equal(false)
expect(result.state).to_equal("missing-api-tls-key-create")
expect(result.thread_features).to_contain("pthread")
expect(result.thread_features).to_contain("mutex")
```

</details>

#### derives a ready Wine thread gate from the full adapter surface

- derives a ready Wine thread gate from the full adapter surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives a ready Wine thread gate from the full adapter surface")
val features = wine_thread_adapter_feature_string(_all_thread_apis())
expect(features).to_contain("pthread")
expect(features).to_contain("tls")
expect(features).to_contain("thread-fault")
```

</details>

#### accepts the full thread/TLS/wait-object adapter API set

- accepts the full thread/TLS/wait-object adapter API set
   - Expected: result.ready is true
   - Expected: result.state equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the full thread/TLS/wait-object adapter API set")
val result = wine_thread_adapter_gate(_all_thread_apis())
expect(result.ready).to_equal(true)
expect(result.state).to_equal("ready")
```

</details>

#### requires modeled NT thread wait completion before full adapter readiness

- requires modeled NT thread wait completion before full adapter readiness
   - Expected: result.ready is true
   - Expected: result.state equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires modeled NT thread wait completion before full adapter readiness")
val created = wine_nt_create_thread(wine_nt_thread_table_new(_all_thread_apis()), "main", 7)
val waited = wine_nt_wait_for_single_object(created.table, created.handle, 1000)
val result = wine_thread_adapter_gate_with_wait_result(_all_thread_apis(), waited)
expect(result.ready).to_equal(true)
expect(result.state).to_equal("ready")
expect(result.thread_features).to_contain("nt-thread-wait")
```

</details>

#### keeps thread adapter readiness blocked on timeout or invalid wait evidence

- keeps thread adapter readiness blocked on timeout or invalid wait evidence
   - Expected: timed.ready is false
   - Expected: timed.state equals `thread-wait-not-signaled:WAIT_TIMEOUT`
   - Expected: errored.ready is false
   - Expected: errored.state equals `thread-wait-invalid-handle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps thread adapter readiness blocked on timeout or invalid wait evidence")
val pending = wine_nt_create_pending_thread(wine_nt_thread_table_new(_all_thread_apis()), "worker")
val timeout = wine_nt_wait_for_single_object(pending.table, pending.handle, 0)
val timed = wine_thread_adapter_gate_with_wait_result(_all_thread_apis(), timeout)
expect(timed.ready).to_equal(false)
expect(timed.state).to_equal("thread-wait-not-signaled:WAIT_TIMEOUT")

val invalid = wine_nt_wait_for_single_object(wine_nt_thread_table_new(_all_thread_apis()), 0x999, 0)
val errored = wine_thread_adapter_gate_with_wait_result(_all_thread_apis(), invalid)
expect(errored.ready).to_equal(false)
expect(errored.state).to_equal("thread-wait-invalid-handle")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_thread_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine thread adapter contract.
- Wine thread adapter contract

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

- Canonical SPipe generation for source `03be3c82d51351c42fe25bb607b5ad557f9695dd41860445f5aaf573fa36b242`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `03be3c82d51351c42fe25bb607b5ad557f9695dd41860445f5aaf573fa36b242`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `03be3c82d51351c42fe25bb607b5ad557f9695dd41860445f5aaf573fa36b242`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/wine_thread_adapter_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_thread_adapter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_thread_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_thread_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_thread_adapter_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists pthread, TLS, synchronization, wait-object, and fault APIs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_thread_adapter_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the first missing thread adapter API' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_thread_adapter_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps currently available thread SFFI calls to their runtime symbols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
