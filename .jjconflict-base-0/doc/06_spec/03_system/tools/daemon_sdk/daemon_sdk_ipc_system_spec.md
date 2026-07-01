# daemon_sdk_ipc_system_spec

> @cover src/lib/nogc_async_mut/mcp/__init__.spl 60%

<!-- sdn-diagram:id=daemon_sdk_ipc_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=daemon_sdk_ipc_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

daemon_sdk_ipc_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=daemon_sdk_ipc_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# daemon_sdk_ipc_system_spec

@cover src/lib/nogc_async_mut/mcp/__init__.spl 60%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DSDK-SYS-001 to #DSDK-SYS-010 |
| Category | Infrastructure / System Test |
| Status | Active |
| Source | `test/03_system/tools/daemon_sdk/daemon_sdk_ipc_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/lib/nogc_async_mut/mcp/__init__.spl 60%
Daemon SDK IPC System Test

Tests real file-based IPC: writes actual .req/.resp files to disk,
verifies serialization/deserialization, atomic writes, and cleanup.
Uses a temp directory under /tmp to avoid polluting the project.

## Scenarios

### DaemonSDK System IPC

### request file I/O

#### writes and reads request file

1. sys setup
   - Expected: rt_file_exists(path) is true
2. sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sys_setup()
val path = write_req_file("test_1", 1, [("test_path", "test/foo_spec.spl")])
expect(rt_file_exists(path)).to_equal(true)
val content = read_file_content(path)
expect(content).to_contain("id=test_1")
expect(content).to_contain("kind=1")
expect(content).to_contain("field.test_path=test/foo_spec.spl")
sys_cleanup()
```

</details>

#### writes multiple request files

1. sys setup
2. write req file
3. write req file
4. write req file
   - Expected: sys_req_count() equals `3`
5. sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sys_setup()
write_req_file("r1", 1, [])
write_req_file("r2", 2, [])
write_req_file("r3", 3, [])
expect(sys_req_count()).to_equal(3)
sys_cleanup()
```

</details>

#### serializes multiple fields

1. sys setup
2. sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sys_setup()
val path = write_req_file("r_multi", 1, [("path", "test.spl"), ("filter", "unit"), ("clean", "true")])
val content = read_file_content(path)
expect(content).to_contain("field.path=test.spl")
expect(content).to_contain("field.filter=unit")
expect(content).to_contain("field.clean=true")
sys_cleanup()
```

</details>

### response file I/O

#### writes and reads response file

1. sys setup
   - Expected: rt_file_exists(path) is true
2. sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sys_setup()
val path = write_resp_file("req_1", 2, [("passed", "10"), ("failed", "0")])
expect(rt_file_exists(path)).to_equal(true)
val content = read_file_content(path)
expect(content).to_contain("request_id=req_1")
expect(content).to_contain("status=2")
expect(content).to_contain("field.passed=10")
sys_cleanup()
```

</details>

#### writes multiple response files

1. sys setup
2. write resp file
3. write resp file
   - Expected: sys_resp_count() equals `2`
4. sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sys_setup()
write_resp_file("r1", 2, [])
write_resp_file("r2", 3, [])
expect(sys_resp_count()).to_equal(2)
sys_cleanup()
```

</details>

### lock file

#### writes and reads PID from lock

1. sys setup
2. write lock file
   - Expected: first_line equals `54321`
3. sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sys_setup()
write_lock_file(54321)
val content = read_file_content(sys_get_lock())
val first_line = content.split("\n")[0]
expect(first_line).to_equal("54321")
sys_cleanup()
```

</details>

#### detects lock file existence

1. sys setup
   - Expected: rt_file_exists(sys_get_lock()) is false
2. write lock file
   - Expected: rt_file_exists(sys_get_lock()) is true
3. sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sys_setup()
expect(rt_file_exists(sys_get_lock())).to_equal(false)
write_lock_file(12345)
expect(rt_file_exists(sys_get_lock())).to_equal(true)
sys_cleanup()
```

</details>

### cleanup

#### deletes request files

1. sys setup
   - Expected: sys_req_count() equals `2`
2. rt file delete
   - Expected: sys_req_count() equals `1`
3. rt file delete
   - Expected: sys_req_count() equals `0`
4. sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sys_setup()
val p1 = write_req_file("r1", 1, [])
val p2 = write_req_file("r2", 1, [])
expect(sys_req_count()).to_equal(2)
rt_file_delete(p1)
expect(sys_req_count()).to_equal(1)
rt_file_delete(p2)
expect(sys_req_count()).to_equal(0)
sys_cleanup()
```

</details>

#### deletes response files

1. sys setup
   - Expected: sys_resp_count() equals `1`
2. rt file delete
   - Expected: sys_resp_count() equals `0`
3. sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sys_setup()
val p1 = write_resp_file("r1", 2, [])
expect(sys_resp_count()).to_equal(1)
rt_file_delete(p1)
expect(sys_resp_count()).to_equal(0)
sys_cleanup()
```

</details>

### concurrent writes

#### handles rapid sequential writes

1. sys setup
2. write rapid requests
   - Expected: sys_req_count() equals `20`
3. sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sys_setup()
write_rapid_requests(20)
expect(sys_req_count()).to_equal(20)
sys_cleanup()
```

</details>

#### handles interleaved request and response writes

1. sys setup
2. write req file
3. write resp file
4. write req file
5. write resp file
6. write req file
7. write resp file
   - Expected: sys_req_count() equals `3`
   - Expected: sys_resp_count() equals `3`
8. sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sys_setup()
write_req_file("ir_1", 1, [])
write_resp_file("ir_1", 2, [])
write_req_file("ir_2", 1, [])
write_resp_file("ir_2", 3, [])
write_req_file("ir_3", 1, [])
write_resp_file("ir_3", 2, [])
expect(sys_req_count()).to_equal(3)
expect(sys_resp_count()).to_equal(3)
sys_cleanup()
```

</details>

### field extraction

#### extracts specific field from response

1. sys setup
   - Expected: extract_kv_from(content, "field.output=") equals `all tests passed`
   - Expected: extract_kv_from(content, "field.duration_ms=") equals `1500`
2. sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sys_setup()
val path = write_resp_file("ext_1", 2, [("output", "all tests passed"), ("duration_ms", "1500")])
val content = read_file_content(path)
expect(extract_kv_from(content, "field.output=")).to_equal("all tests passed")
expect(extract_kv_from(content, "field.duration_ms=")).to_equal("1500")
sys_cleanup()
```

</details>

#### returns empty for missing field

1. sys setup
   - Expected: extract_kv_from(content, "field.nonexistent=") equals ``
2. sys cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sys_setup()
val path = write_resp_file("ext_2", 2, [])
val content = read_file_content(path)
expect(extract_kv_from(content, "field.nonexistent=")).to_equal("")
sys_cleanup()
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
