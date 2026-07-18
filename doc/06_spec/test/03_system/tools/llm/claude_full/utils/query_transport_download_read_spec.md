# Claude Full Query, Transport, Download, and Read Utilities

> Checks modern SSpec parity for four utility classes.

<!-- sdn-diagram:id=query_transport_download_read_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_transport_download_read_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_transport_download_read_spec -> std
query_transport_download_read_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_transport_download_read_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Query, Transport, Download, and Read Utilities

Checks modern SSpec parity for four utility classes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/query_transport_download_read_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for four utility classes.

## Scenarios

### Claude full query transport download read utilities

#### should guard query lifecycle generations

- var guard = QueryGuard new
   - Expected: reserved.ok is true
   - Expected: guard.isActive() is true
   - Expected: started.ok is true
   - Expected: started.generation equals `1`
   - Expected: guard.tryStart().ok is false
   - Expected: ended.ok is true
   - Expected: ended.guard.getSnapshot() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var guard = QueryGuard.new()
val reserved = guard.reserve()
expect(reserved.ok).to_equal(true)
guard = reserved.guard
expect(guard.isActive()).to_equal(true)
val started = guard.tryStart()
expect(started.ok).to_equal(true)
expect(started.generation).to_equal(1)
guard = started.guard
expect(guard.tryStart().ok).to_equal(false)
val ended = guard.end(1)
expect(ended.ok).to_equal(true)
expect(ended.guard.getSnapshot()).to_equal(false)
```

</details>

#### should model websocket start send receive and close

- var transport = WebSocketTransport new
   - Expected: started.ok is true
   - Expected: sent.ok is true
- transport = sent transport receiveText
   - Expected: transport.sentMessages.len() equals `1`
   - Expected: transport.receivedMethods[0] equals `tools/list`
- transport = transport close
   - Expected: transport.listenersAttached is false
   - Expected: transport.closeCount equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var transport = WebSocketTransport.new(WS_OPEN, false)
val started = transport.start()
expect(started.ok).to_equal(true)
transport = started.transport
val sent = transport.send(JsonRpcMessage.new("1", "initialize", "{}"))
expect(sent.ok).to_equal(true)
transport = sent.transport.receiveText("{\"method\":\"tools/list\"}")
expect(transport.sentMessages.len()).to_equal(1)
expect(transport.receivedMethods[0]).to_equal("tools/list")
transport = transport.close()
expect(transport.listenersAttached).to_equal(false)
expect(transport.closeCount).to_equal(1)
```

</details>

#### should model download stall retry and checksum verification

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stalled = downloadAndVerifyBinaryPlan([DownloadAttempt.stalled(), DownloadAttempt.ok(44, "abc")], "abc")
expect(stalled.ok).to_equal(true)
expect(stalled.attempts).to_equal(2)
expect(getStallTimeoutMs(123)).to_equal(123)
val mismatch = downloadAndVerifyBinaryPlan([DownloadAttempt.ok(9, "bad")], "good")
expect(mismatch.ok).to_equal(false)
expect(mismatch.message).to_contain("Checksum mismatch")
expect(StallTimeoutError.new().name).to_equal("StallTimeoutError")
```

</details>

#### should model file range limits and truncation

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(chooseReadPath(true, 10)).to_equal("fast")
expect(chooseReadPath(false, 10)).to_equal("streaming")
val tooLarge = readFileInRangeFastModel("a\nb", 99, 0, 0, 10, false)
expect(tooLarge.error.name).to_equal("FileTooLargeError")
val selected = readFileInRangeFastModel("a\r\nb\r\nc", 5, 1, 1, 0, false)
expect(selected.content).to_equal("b")
expect(selected.lineCount).to_equal(1)
val truncated = readFileInRangeFastModel("abcdef", 6, 0, 1, 3, true)
expect(truncated.truncatedByBytes).to_equal(true)
expect(truncated.content).to_equal("abc")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mcpWebSocketTransportSourceLinesModeled()).to_equal(200)
expect(nativeDownloadSourceLinesModeled()).to_equal(523)
expect(queryGuardSourceLinesModeled()).to_equal(121)
expect(readFileInRangeSourceLinesModeled()).to_equal(383)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
