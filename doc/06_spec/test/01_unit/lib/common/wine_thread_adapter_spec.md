# Wine Thread Adapter Specification

> <details>

<!-- sdn-diagram:id=wine_thread_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_thread_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_thread_adapter_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_thread_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Thread Adapter Specification

## Scenarios

### Wine thread adapter contract

#### lists pthread, TLS, synchronization, wait-object, and fault APIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val apis = wine_thread_adapter_required_apis()
expect(apis.len()).to_be_greater_than(20)
expect(apis[0]).to_equal("thread-create")
```

</details>

#### reports the first missing thread adapter API

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = wine_thread_adapter_missing_apis("thread-create thread-join")
expect(missing[0]).to_equal("thread-detach")
```

</details>

#### maps currently available thread SFFI calls to their runtime symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_thread_adapter_sffi_binding("thread-create")).to_equal("spl_thread_create")
expect(wine_thread_adapter_sffi_binding("mutex-try-lock")).to_equal("spl_mutex_try_lock")
expect(wine_thread_adapter_sffi_binding("condvar-wait-timeout")).to_equal("spl_condvar_wait_timeout")
```

</details>

#### shows existing thread SFFI still lacks Wine TLS and wait objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_thread_adapter_gate(_existing_thread_sffi_apis())
expect(result.ready).to_equal(false)
expect(result.state).to_equal("missing-api-tls-key-create")
expect(result.thread_features).to_contain("pthread")
expect(result.thread_features).to_contain("mutex")
```

</details>

#### derives a ready Wine thread gate from the full adapter surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = wine_thread_adapter_feature_string(_all_thread_apis())
expect(features).to_contain("pthread")
expect(features).to_contain("tls")
expect(features).to_contain("thread-fault")
```

</details>

#### accepts the full thread/TLS/wait-object adapter API set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_thread_adapter_gate(_all_thread_apis())
expect(result.ready).to_equal(true)
expect(result.state).to_equal("ready")
```

</details>

#### requires modeled NT thread wait completion before full adapter readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val created = wine_nt_create_thread(wine_nt_thread_table_new(_all_thread_apis()), "main", 7)
val waited = wine_nt_wait_for_single_object(created.table, created.handle, 1000)
val result = wine_thread_adapter_gate_with_wait_result(_all_thread_apis(), waited)
expect(result.ready).to_equal(true)
expect(result.state).to_equal("ready")
expect(result.thread_features).to_contain("nt-thread-wait")
```

</details>

#### keeps thread adapter readiness blocked on timeout or invalid wait evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
