# watcher_protocol_spec

> Watcher Protocol Specification

<!-- sdn-diagram:id=watcher_protocol_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=watcher_protocol_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

watcher_protocol_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=watcher_protocol_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# watcher_protocol_spec

Watcher Protocol Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WATCH-021 to #WATCH-030 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/compiler/watcher/watcher_protocol_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Watcher Protocol Specification

Tests file-based request/response protocol for watcher IPC.

## Scenarios

### WatcherProtocol

### write_request

#### creates request file in request directory

1. proto reset
   - Expected: proto_exists(path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
proto_reset()
val path = mock_write_request("src/main.spl", "shb", ".build/watcher/requests")
expect(path).to_end_with(".req")
expect(proto_exists(path)).to_equal(true)
```

</details>

#### serializes source_path and kind

1. proto reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
proto_reset()
val path = mock_write_request("src/lib/math.spl", "smf", ".build/watcher/requests")
val content = proto_read(path)
expect(content).to_contain("source_path=src/lib/math.spl")
expect(content).to_contain("kind=smf")
```

</details>

### read_requests

#### reads all request files

1. proto reset
2. mock write request
3. mock write request
   - Expected: requests.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
proto_reset()
mock_write_request("src/a.spl", "shb", ".build/watcher/requests")
mock_write_request("src/b.spl", "smf", ".build/watcher/requests")
val requests = mock_read_requests(".build/watcher/requests")
expect(requests.len()).to_equal(2)
```

</details>

#### returns empty for no requests

1. proto reset
   - Expected: requests.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
proto_reset()
val requests = mock_read_requests(".build/watcher/requests")
expect(requests.len()).to_equal(0)
```

</details>

#### parses source_path and kind correctly

1. proto reset
2. mock write request
   - Expected: requests[0][0] equals `src/main.spl`
   - Expected: requests[0][1] equals `both`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
proto_reset()
mock_write_request("src/main.spl", "both", ".build/watcher/requests")
val requests = mock_read_requests(".build/watcher/requests")
expect(requests[0][0]).to_equal("src/main.spl")
expect(requests[0][1]).to_equal("both")
```

</details>

### request_path_for

#### generates deterministic path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path1 = make_req_path("src/main.spl", ".build/watcher/requests")
val path2 = make_req_path("src/main.spl", ".build/watcher/requests")
expect(path1).to_equal(path2)
```

</details>

#### generates different paths for different sources

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path1 = make_req_path("src/a.spl", ".build/watcher/requests")
val path2 = make_req_path("src/b.spl", ".build/watcher/requests")
expect(path1 != path2).to_equal(true)
```

</details>

### cleanup

#### deletes processed request files

1. proto reset
   - Expected: proto_exists(path) is true
2. proto delete
   - Expected: proto_exists(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
proto_reset()
val path = mock_write_request("src/main.spl", "shb", ".build/watcher/requests")
expect(proto_exists(path)).to_equal(true)
proto_delete(path)
expect(proto_exists(path)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
