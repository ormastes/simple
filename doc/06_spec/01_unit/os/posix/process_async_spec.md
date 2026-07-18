# Async Process Specification

> Native SimpleOS process control is async-first. POSIX process wrappers block

<!-- sdn-diagram:id=process_async_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=process_async_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

process_async_spec -> std
process_async_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=process_async_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/os/posix/process_async_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Native SimpleOS process control is async-first. POSIX process wrappers block
over this request facade.

## Scenarios

### process_async request lifecycle

#### completes invalid spawn paths without entering the syscall backend

1. process async init
   - Expected: process_async_is_complete(req) is true
   - Expected: process_async_result(req) equals `0 - EINVAL as i64`
2. process async free request


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
process_async_init()
val req = process_async_spawn("", [], 2)

expect(req).to_be_less_than(PROCESS_MAX_REQUESTS)
expect(process_async_is_complete(req)).to_equal(true)
expect(process_async_result(req)).to_equal(0 - EINVAL as i64)

process_async_free_request(req)
```

</details>

#### completes invalid exec paths without entering the syscall backend

1. process async init
   - Expected: process_async_is_complete(req) is true
   - Expected: process_async_result(req) equals `0 - EINVAL as i64`
2. process async free request


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
process_async_init()
val req = process_async_execve("", [], [])

expect(req).to_be_less_than(PROCESS_MAX_REQUESTS)
expect(process_async_is_complete(req)).to_equal(true)
expect(process_async_result(req)).to_equal(0 - EINVAL as i64)

process_async_free_request(req)
```

</details>

#### completes invalid signal requests without entering the syscall backend

1. process async init
   - Expected: process_async_is_complete(req) is true
   - Expected: process_async_result(req) equals `0 - EINVAL as i64`
2. process async free request


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
process_async_init()
val req = process_async_signal(42u64, -1)

expect(req).to_be_less_than(PROCESS_MAX_REQUESTS)
expect(process_async_is_complete(req)).to_equal(true)
expect(process_async_result(req)).to_equal(0 - EINVAL as i64)

process_async_free_request(req)
```

</details>

#### reports EIO for invalid request handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
