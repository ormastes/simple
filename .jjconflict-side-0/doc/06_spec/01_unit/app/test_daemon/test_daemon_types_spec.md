# test_daemon_types_spec

> Test Daemon Types Specification

<!-- sdn-diagram:id=test_daemon_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_types_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_daemon_types_spec

Test Daemon Types Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TDMN-001 to #TDMN-010 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/app/test_daemon/test_daemon_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Test Daemon Types Specification

Tests test-specific request kinds, response statuses,
configuration, and conversion functions.

## Scenarios

### TestDaemonConfig

#### has correct default lock path

1. tcfg reset
   - Expected: tcfg_get_lock() equals `.build/test_daemon/test_daemon.lock`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
tcfg_reset()
expect(tcfg_get_lock()).to_equal(".build/test_daemon/test_daemon.lock")
```

</details>

#### has correct default cache path

1. tcfg reset
   - Expected: tcfg_get_cache() equals `.build/test_daemon/test_cache.sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
tcfg_reset()
expect(tcfg_get_cache()).to_equal(".build/test_daemon/test_cache.sdn")
```

</details>

#### has correct default QEMU timeout

1. tcfg reset
   - Expected: tcfg_get_qemu_timeout() equals `300000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
tcfg_reset()
expect(tcfg_get_qemu_timeout()).to_equal(300000)
```

</details>

#### has correct default max QEMU sessions

1. tcfg reset
   - Expected: tcfg_get_max_qemu() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
tcfg_reset()
expect(tcfg_get_max_qemu()).to_equal(4)
```

</details>

### TestRequestConversion

#### converts RUN_SINGLE with path

1. treq reset
2. treq create
   - Expected: fields.len() equals `1`
   - Expected: fields[0][0] equals `test_path`
   - Expected: fields[0][1] equals `test/foo_spec.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
treq_reset()
treq_create(TREQ_RUN_SINGLE, "test/foo_spec.spl", "", false)
val fields = treq_to_daemon_fields()
expect(fields.len()).to_equal(1)
expect(fields[0][0]).to_equal("test_path")
expect(fields[0][1]).to_equal("test/foo_spec.spl")
```

</details>

#### converts CLEAN_RUN with clean flag

1. treq reset
2. treq create
   - Expected: fields.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
treq_reset()
treq_create(TREQ_CLEAN_RUN, "test/bar_spec.spl", "", true)
val fields = treq_to_daemon_fields()
expect(fields.len()).to_equal(2)
```

</details>

#### converts RUN_ALL with filter

1. treq reset
2. treq create
   - Expected: fields.len() equals `1`
   - Expected: fields[0][0] equals `filter`
   - Expected: fields[0][1] equals `unit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
treq_reset()
treq_create(TREQ_RUN_ALL, "", "unit", false)
val fields = treq_to_daemon_fields()
expect(fields.len()).to_equal(1)
expect(fields[0][0]).to_equal("filter")
expect(fields[0][1]).to_equal("unit")
```

</details>

#### preserves request kind

1. treq reset
2. treq create
   - Expected: treq_get_kind() equals `TREQ_STATUS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
treq_reset()
treq_create(TREQ_STATUS, "", "", false)
expect(treq_get_kind()).to_equal(TREQ_STATUS)
```

</details>

### TestResponseConversion

#### parses completed result

1. tresp reset
2. tresp from fields
   - Expected: tresp_get_status() equals `TRESP_COMPLETED`
   - Expected: tresp_get_passed() equals `10`
   - Expected: tresp_get_failed() equals `0`
   - Expected: tresp_get_cached() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
tresp_reset()
tresp_from_fields(TRESP_COMPLETED, "10", "0", "2", "450", "false")
expect(tresp_get_status()).to_equal(TRESP_COMPLETED)
expect(tresp_get_passed()).to_equal(10)
expect(tresp_get_failed()).to_equal(0)
expect(tresp_get_cached()).to_equal(false)
```

</details>

#### parses cached result

1. tresp reset
2. tresp from fields
   - Expected: tresp_get_status() equals `TRESP_CACHED`
   - Expected: tresp_get_cached() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
tresp_reset()
tresp_from_fields(TRESP_CACHED, "5", "0", "0", "0", "true")
expect(tresp_get_status()).to_equal(TRESP_CACHED)
expect(tresp_get_cached()).to_equal(true)
```

</details>

#### parses failed result

1. tresp reset
2. tresp from fields
   - Expected: tresp_get_status() equals `TRESP_FAILED`
   - Expected: tresp_get_failed() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
tresp_reset()
tresp_from_fields(TRESP_FAILED, "3", "2", "0", "800", "false")
expect(tresp_get_status()).to_equal(TRESP_FAILED)
expect(tresp_get_failed()).to_equal(2)
```

</details>

### RequestKindConstants

#### has distinct values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TREQ_RUN_SINGLE != TREQ_RUN_ALL).to_equal(true)
expect(TREQ_RUN_ALL != TREQ_CLEAN_RUN).to_equal(true)
expect(TREQ_CLEAN_RUN != TREQ_STATUS).to_equal(true)
expect(TREQ_STATUS != TREQ_STOP).to_equal(true)
```

</details>

### ResponseStatusConstants

#### has distinct values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TRESP_QUEUED != TRESP_COMPLETED).to_equal(true)
expect(TRESP_COMPLETED != TRESP_FAILED).to_equal(true)
expect(TRESP_FAILED != TRESP_CACHED).to_equal(true)
expect(TRESP_CACHED != TRESP_ERROR).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
