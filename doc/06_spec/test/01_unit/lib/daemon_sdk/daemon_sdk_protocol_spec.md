# daemon_sdk_protocol_spec

> Daemon SDK Protocol Specification

<!-- sdn-diagram:id=daemon_sdk_protocol_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=daemon_sdk_protocol_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

daemon_sdk_protocol_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=daemon_sdk_protocol_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# daemon_sdk_protocol_spec

Daemon SDK Protocol Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DSDK-021 to #DSDK-030 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/lib/daemon_sdk/daemon_sdk_protocol_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Daemon SDK Protocol Specification

Tests file-based IPC: request/response serialization, atomic writes,
field extraction, and cleanup.

## Scenarios

### DaemonProtocol

### write_request

#### creates .req file in request directory

1. fs reset
   - Expected: fs_exists(path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs_reset()
val path = mock_write_request("pid_100", 1, [], [], ".build/daemon/requests")
expect(path).to_end_with(".req")
expect(fs_exists(path)).to_equal(true)
```

</details>

#### serializes id and kind

1. fs reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs_reset()
val path = mock_write_request("pid_200", 3, [], [], ".build/daemon/requests")
val content = fs_read(path)
expect(content).to_contain("id=pid_200")
expect(content).to_contain("kind=3")
```

</details>

#### serializes arbitrary fields

1. fs reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs_reset()
val path = mock_write_request("pid_300", 1, ["test_path", "filter"], ["test/foo_spec.spl", "unit"], ".build/daemon/requests")
val content = fs_read(path)
expect(content).to_contain("field.test_path=test/foo_spec.spl")
expect(content).to_contain("field.filter=unit")
```

</details>

#### includes timestamp

1. fs reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs_reset()
val path = mock_write_request("pid_400", 1, [], [], ".build/daemon/requests")
val content = fs_read(path)
expect(content).to_contain("timestamp=")
```

</details>

### write_response

#### creates .resp file

1. fs reset
2. mock write response
   - Expected: fs_exists(".build/daemon/responses/pid_100.resp") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs_reset()
mock_write_response("pid_100", 2, [], [], ".build/daemon/responses")
expect(fs_exists(".build/daemon/responses/pid_100.resp")).to_equal(true)
```

</details>

#### serializes request_id and status

1. fs reset
2. mock write response


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs_reset()
mock_write_response("pid_200", 3, [], [], ".build/daemon/responses")
val content = fs_read(".build/daemon/responses/pid_200.resp")
expect(content).to_contain("request_id=pid_200")
expect(content).to_contain("status=3")
```

</details>

#### serializes response fields

1. fs reset
2. mock write response


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs_reset()
mock_write_response("pid_300", 2, ["passed", "failed"], ["5", "0"], ".build/daemon/responses")
val content = fs_read(".build/daemon/responses/pid_300.resp")
expect(content).to_contain("field.passed=5")
expect(content).to_contain("field.failed=0")
```

</details>

### read_requests

#### reads all pending requests

1. fs reset
2. mock write request
3. mock write request
4. mock write request
   - Expected: reqs.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs_reset()
mock_write_request("r1", 1, [], [], ".build/daemon/requests")
mock_write_request("r2", 2, [], [], ".build/daemon/requests")
mock_write_request("r3", 3, [], [], ".build/daemon/requests")
val reqs = mock_read_requests(".build/daemon/requests")
expect(reqs.len()).to_equal(3)
```

</details>

#### returns empty when no requests

1. fs reset
   - Expected: reqs.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs_reset()
val reqs = mock_read_requests(".build/daemon/requests")
expect(reqs.len()).to_equal(0)
```

</details>

#### parses id and kind correctly

1. fs reset
2. mock write request
   - Expected: reqs[0][0] equals `req_abc`
   - Expected: reqs[0][1] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs_reset()
mock_write_request("req_abc", 5, [], [], ".build/daemon/requests")
val reqs = mock_read_requests(".build/daemon/requests")
expect(reqs[0][0]).to_equal("req_abc")
expect(reqs[0][1]).to_equal(5)
```

</details>

### read_response

#### reads existing response

1. fs reset
2. mock write response
   - Expected: resp[0] equals `req_1`
   - Expected: resp[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs_reset()
mock_write_response("req_1", 2, [], [], ".build/daemon/responses")
val resp = mock_read_response("req_1", ".build/daemon/responses")
expect(resp[0]).to_equal("req_1")
expect(resp[1]).to_equal(2)
```

</details>

#### returns empty for missing response

1. fs reset
   - Expected: resp[0] equals ``
   - Expected: resp[1] equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs_reset()
val resp = mock_read_response("nonexistent", ".build/daemon/responses")
expect(resp[0]).to_equal("")
expect(resp[1]).to_equal(-1)
```

</details>

### field extraction

#### extracts named fields from response

1. fs reset
2. mock write response
   - Expected: extract_field_kv(content, "output") equals `OK`
   - Expected: extract_field_kv(content, "duration_ms") equals `150`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs_reset()
mock_write_response("r1", 2, ["output", "duration_ms"], ["OK", "150"], ".build/daemon/responses")
val content = fs_read(".build/daemon/responses/r1.resp")
expect(extract_field_kv(content, "output")).to_equal("OK")
expect(extract_field_kv(content, "duration_ms")).to_equal("150")
```

</details>

#### returns empty for missing fields

1. fs reset
2. mock write response
   - Expected: extract_field_kv(content, "nonexistent") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs_reset()
mock_write_response("r1", 2, [], [], ".build/daemon/responses")
val content = fs_read(".build/daemon/responses/r1.resp")
expect(extract_field_kv(content, "nonexistent")).to_equal("")
```

</details>

### cleanup

#### deletes processed request files

1. fs reset
   - Expected: fs_get_count() equals `2`
2. fs delete
   - Expected: fs_get_count() equals `1`
   - Expected: fs_exists(p1) is false
   - Expected: fs_exists(p2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs_reset()
val p1 = mock_write_request("r1", 1, [], [], ".build/requests")
val p2 = mock_write_request("r2", 1, [], [], ".build/requests")
expect(fs_get_count()).to_equal(2)
fs_delete(p1)
expect(fs_get_count()).to_equal(1)
expect(fs_exists(p1)).to_equal(false)
expect(fs_exists(p2)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
