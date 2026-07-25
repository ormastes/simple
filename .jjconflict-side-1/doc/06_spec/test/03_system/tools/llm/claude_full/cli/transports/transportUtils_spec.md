# Claude Full Transport Utils

> Checks transport selection priority for Claude CLI session ingress URLs.

<!-- sdn-diagram:id=transportUtils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=transportUtils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

transportUtils_spec -> std
transportUtils_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=transportUtils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Transport Utils

Checks transport selection priority for Claude CLI session ingress URLs.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/transports/transportUtils_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks transport selection priority for Claude CLI session ingress URLs.

## Scenarios

### Claude full transport utils

#### should prefer SSE transport when CCR v2 is enabled

- Select transport for secure websocket URL
   - Expected: choice.kind equals `SSETransport`
   - Expected: choice.url equals `https://api.example/session/1/worker/events/stream`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Select transport for secure websocket URL")
val choice = getTransportForUrl("wss://api.example/session/1", true, false)
expect(choice.kind).to_equal("SSETransport")
expect(choice.url).to_equal("https://api.example/session/1/worker/events/stream")
```

</details>

#### should convert insecure websocket SSE URLs to HTTP

- Select transport for local websocket URL
   - Expected: choice.kind equals `SSETransport`
   - Expected: choice.url equals `http://localhost/session/1/worker/events/stream`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Select transport for local websocket URL")
val choice = getTransportForUrl("ws://localhost/session/1/", true, false)
expect(choice.kind).to_equal("SSETransport")
expect(choice.url).to_equal("http://localhost/session/1/worker/events/stream")
```

</details>

#### should choose hybrid for websocket ingress post flag

- Select post-for-ingress transport
   - Expected: choice.kind equals `HybridTransport`
   - Expected: choice.url equals `wss://api.example/session/1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Select post-for-ingress transport")
val choice = getTransportForUrl("wss://api.example/session/1", false, true)
expect(choice.kind).to_equal("HybridTransport")
expect(choice.url).to_equal("wss://api.example/session/1")
```

</details>

#### should choose websocket by default

- Select default websocket transport
   - Expected: choice.kind equals `WebSocketTransport`
   - Expected: choice.error equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Select default websocket transport")
val choice = getTransportForUrl("ws://localhost/session/1", false, false)
expect(choice.kind).to_equal("WebSocketTransport")
expect(choice.error).to_equal("")
```

</details>

#### should reject unsupported protocols

- Select transport for HTTPS URL without CCR v2
   - Expected: choice.kind equals ``
   - Expected: choice.error equals `Unsupported protocol: https:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Select transport for HTTPS URL without CCR v2")
val choice = getTransportForUrl("https://api.example/session/1", false, false)
expect(choice.kind).to_equal("")
expect(choice.error).to_equal("Unsupported protocol: https:")
```

</details>

#### should expose source line parity

- Pin source size
   - Expected: transportUtilsSourceLinesModeled() equals `45`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin source size")
expect(transportUtilsSourceLinesModeled()).to_equal(45)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
