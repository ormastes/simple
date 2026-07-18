# Claude Full REPL Bridge Handle

> Mirrors the active REPL bridge handle slot and compat session-id publication.

<!-- sdn-diagram:id=replBridgeHandle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replBridgeHandle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replBridgeHandle_spec -> std
replBridgeHandle_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replBridgeHandle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full REPL Bridge Handle

Mirrors the active REPL bridge handle slot and compat session-id publication.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/bridge/replBridgeHandle_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors the active REPL bridge handle slot and compat session-id publication.

## Scenarios

### Claude full REPL bridge handle

#### stores and returns the active bridge handle

- Set a connected handle in the process-global slot model
- slot setReplBridgeHandle
   - Expected: handle.bridgeSessionId equals `cse_abc`
   - Expected: handle.environmentId equals `env_1`
   - Expected: handle.hasSession() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Set a connected handle in the process-global slot model")
val slot = ReplBridgeHandleSlot.new()
slot.setReplBridgeHandle(ReplBridgeHandle.new("cse_abc", "env_1"))
val handle = getReplBridgeHandle(slot)
expect(handle.bridgeSessionId).to_equal("cse_abc")
expect(handle.environmentId).to_equal("env_1")
expect(handle.hasSession()).to_equal(true)
```

</details>

#### publishes compat session ids on set

- Convert cse ids to session format
- slot setReplBridgeHandle
   - Expected: getSelfBridgeCompatId(slot) equals `session_123`
   - Expected: slot.publishedCompatId equals `session_123`
   - Expected: slot.updateAttempts equals `1`
   - Expected: toCompatSessionId("session_existing") equals `session_existing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Convert cse ids to session format")
val slot = ReplBridgeHandleSlot.new()
slot.setReplBridgeHandle(ReplBridgeHandle.new("cse_123", "env_2"))
expect(getSelfBridgeCompatId(slot)).to_equal("session_123")
expect(slot.publishedCompatId).to_equal("session_123")
expect(slot.updateAttempts).to_equal(1)
expect(toCompatSessionId("session_existing")).to_equal("session_existing")
```

</details>

#### clears the handle and publishes a clear value

- Clear on teardown
- slot setReplBridgeHandle
- slot clearReplBridgeHandle
   - Expected: getReplBridgeHandle(slot).hasSession() is false
   - Expected: getSelfBridgeCompatId(slot) equals ``
   - Expected: slot.hasPublishedClear() is true
   - Expected: slot.updateAttempts equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Clear on teardown")
val slot = ReplBridgeHandleSlot.new()
slot.setReplBridgeHandle(ReplBridgeHandle.new("cse_123", "env_2"))
slot.clearReplBridgeHandle()
expect(getReplBridgeHandle(slot).hasSession()).to_equal(false)
expect(getSelfBridgeCompatId(slot)).to_equal("")
expect(slot.hasPublishedClear()).to_equal(true)
expect(slot.updateAttempts).to_equal(2)
```

</details>

#### ignores empty disconnected handles

- Treat an empty handle like no active bridge
- slot setReplBridgeHandle
   - Expected: getReplBridgeHandle(slot).hasSession() is false
   - Expected: getSelfBridgeCompatId(slot) equals ``
   - Expected: slot.publishedCompatId equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Treat an empty handle like no active bridge")
val slot = ReplBridgeHandleSlot.new()
slot.setReplBridgeHandle(ReplBridgeHandle.empty())
expect(getReplBridgeHandle(slot).hasSession()).to_equal(false)
expect(getSelfBridgeCompatId(slot)).to_equal("")
expect(slot.publishedCompatId).to_equal("")
```

</details>

#### documents the one-bridge-per-process purpose

- Expose tiny constants for debug/manual evidence
   - Expected: replBridgeHandlePurpose() equals `global active REPL bridge handle`
   - Expected: replBridgeHandlePublishReason() equals `dedupe local bridge sessions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expose tiny constants for debug/manual evidence")
expect(replBridgeHandlePurpose()).to_equal("global active REPL bridge handle")
expect(replBridgeHandlePublishReason()).to_equal("dedupe local bridge sessions")
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
