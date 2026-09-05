# SOSIX Process Specification

> SOSIX is the native async process surface. POSIX process APIs are wrappers over

<!-- sdn-diagram:id=process_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=process_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

process_spec -> std
process_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=process_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SOSIX Process Specification

SOSIX is the native async process surface. POSIX process APIs are wrappers over

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/process_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

SOSIX is the native async process surface. POSIX process APIs are wrappers over
this module.

## Scenarios

### SOSIX process request lifecycle

#### completes invalid spawn paths without entering the syscall backend

1. sosix process init
   - Expected: sosix_process_is_complete(req) is true
   - Expected: sosix_process_result(req) equals `0 - EINVAL as i64`
2. sosix process free request


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_process_init()
val req = sosix_process_spawn("", [], 2)

expect(req).to_be_less_than(SOSIX_PROCESS_MAX_REQUESTS)
expect(sosix_process_is_complete(req)).to_equal(true)
expect(sosix_process_result(req)).to_equal(0 - EINVAL as i64)

sosix_process_free_request(req)
```

</details>

#### completes invalid exec paths without entering the syscall backend

1. sosix process init
   - Expected: sosix_process_is_complete(req) is true
   - Expected: sosix_process_result(req) equals `0 - EINVAL as i64`
2. sosix process free request


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_process_init()
val req = sosix_process_execve("", [], [])

expect(req).to_be_less_than(SOSIX_PROCESS_MAX_REQUESTS)
expect(sosix_process_is_complete(req)).to_equal(true)
expect(sosix_process_result(req)).to_equal(0 - EINVAL as i64)

sosix_process_free_request(req)
```

</details>

#### completes invalid signal requests without entering the syscall backend

1. sosix process init
   - Expected: sosix_process_is_complete(req) is true
   - Expected: sosix_process_result(req) equals `0 - EINVAL as i64`
2. sosix process free request


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_process_init()
val req = sosix_process_signal(42u64, -1)

expect(req).to_be_less_than(SOSIX_PROCESS_MAX_REQUESTS)
expect(sosix_process_is_complete(req)).to_equal(true)
expect(sosix_process_result(req)).to_equal(0 - EINVAL as i64)

sosix_process_free_request(req)
```

</details>

#### reports EIO for invalid request handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sosix_process_is_complete(SOSIX_PROCESS_MAX_REQUESTS)).to_equal(true)
expect(sosix_process_result(SOSIX_PROCESS_MAX_REQUESTS)).to_equal(0 - EIO as i64)
expect(sosix_process_wait_request(SOSIX_PROCESS_MAX_REQUESTS)).to_equal(0 - EIO as i64)
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
