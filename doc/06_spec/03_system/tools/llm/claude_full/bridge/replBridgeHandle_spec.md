# Claude Full REPL Bridge Handle

> Mirrors the active REPL bridge handle slot and compat session-id publication.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors the active REPL bridge handle slot and compat session-id publication.

## Scenarios

### Claude full REPL bridge handle

#### stores and returns the active bridge handle

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stores and returns the active bridge handle
- Set a connected handle in the process-global slot model
   - Expected: handle.bridgeSessionId equals `cse_abc`
   - Expected: handle.environmentId equals `env_1`
   - Expected: handle.hasSession() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores and returns the active bridge handle")
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

- publishes compat session ids on set
- Convert cse ids to session format
   - Expected: getSelfBridgeCompatId(slot) equals `session_123`
   - Expected: slot.publishedCompatId equals `session_123`
   - Expected: slot.updateAttempts equals `1`
   - Expected: toCompatSessionId("session_existing") equals `session_existing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("publishes compat session ids on set")
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

- clears the handle and publishes a clear value
- Clear on teardown
   - Expected: getReplBridgeHandle(slot).hasSession() is false
   - Expected: getSelfBridgeCompatId(slot) equals ``
   - Expected: slot.hasPublishedClear() is true
   - Expected: slot.updateAttempts equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clears the handle and publishes a clear value")
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

- ignores empty disconnected handles
- Treat an empty handle like no active bridge
   - Expected: getReplBridgeHandle(slot).hasSession() is false
   - Expected: getSelfBridgeCompatId(slot) equals ``
   - Expected: slot.publishedCompatId equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ignores empty disconnected handles")
step("Treat an empty handle like no active bridge")
val slot = ReplBridgeHandleSlot.new()
slot.setReplBridgeHandle(ReplBridgeHandle.empty())
expect(getReplBridgeHandle(slot).hasSession()).to_equal(false)
expect(getSelfBridgeCompatId(slot)).to_equal("")
expect(slot.publishedCompatId).to_equal("")
```

</details>

#### documents the one-bridge-per-process purpose

- documents the one-bridge-per-process purpose
- Expose tiny constants for debug/manual evidence
   - Expected: replBridgeHandlePurpose() equals `global active REPL bridge handle`
   - Expected: replBridgeHandlePublishReason() equals `dedupe local bridge sessions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents the one-bridge-per-process purpose")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ac095f48260b724540fa6b3cc0ff7e4f148f2f47102c646edb4cb4d6ddfcaba4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ac095f48260b724540fa6b3cc0ff7e4f148f2f47102c646edb4cb4d6ddfcaba4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ac095f48260b724540fa6b3cc0ff7e4f148f2f47102c646edb4cb4d6ddfcaba4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/bridge/replBridgeHandle_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/bridge/replBridgeHandle_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/bridge/replBridgeHandle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/bridge/replBridgeHandle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/bridge/replBridgeHandle_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/bridge/replBridgeHandle_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores and returns the active bridge handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/replBridgeHandle_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes compat session ids on set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/replBridgeHandle_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clears the handle and publishes a clear value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
