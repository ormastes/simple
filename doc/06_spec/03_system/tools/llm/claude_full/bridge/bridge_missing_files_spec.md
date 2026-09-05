# Claude Full Bridge Missing Files

> Purpose: should model bridge UI status rendering

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge Missing Files

Purpose: should model bridge UI status rendering

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/bridge/bridge_missing_files_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should model bridge UI status rendering
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Bridge Missing Files

## Overview

Checks deterministic parity surfaces for the six bridge files missing from the
Claude-full llm_caret bridge lane.

## Scenarios

### Claude full bridge missing files

#### should model bridge UI status rendering

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model bridge UI status rendering
- Verify: should model bridge UI status rendering
- Render QR, visual lines, and connecting status
   - Expected: logger.qr.visible is true
   - Expected: logger.statusLines equals `2`
   - Expected: logger.renderConnectingLine(2) equals `Connecting...`
   - Expected: bridgeUISourceLinesModeled() equals `530`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model bridge UI status rendering")
step("Verify: should model bridge UI status rendering")
# @req: REQ-TOOLS-BridMissFile-001
step("Render QR, visual lines, and connecting status")
val logger = createBridgeLogger("https://claude.ai/bridge")
logger.writeStatus("hello\nworld")
expect(logger.qr.visible).to_equal(true)
expect(logger.statusLines).to_equal(2)  # oracle: value fixed by the spec contract
expect(logger.renderConnectingLine(2)).to_equal("Connecting...")
expect(bridgeUISourceLinesModeled()).to_equal(530)  # oracle: value fixed by the spec contract
```

</details>

#### should model bridge session lifecycle

- should model bridge session lifecycle
- Verify: should model bridge session lifecycle
- Create, rename, fetch, and archive a bridge session
   - Expected: getBridgeSession(created, "session_1").title equals `title`
   - Expected: renamed.events[1].kind equals `title`
   - Expected: archived.archived is true
   - Expected: createSessionSourceLinesModeled() equals `384`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model bridge session lifecycle")
step("Verify: should model bridge session lifecycle")
# @req: REQ-TOOLS-BridMissFile-001
step("Create, rename, fetch, and archive a bridge session")
val git = BridgeGitSource.new("main", "git@example/repo", "/repo")
val created = createBridgeSession("session_1", "  title  ", git)
val renamed = updateBridgeSessionTitle(created, "next")
val archived = archiveBridgeSession(renamed)
expect(getBridgeSession(created, "session_1").title).to_equal("title")
expect(renamed.events[1].kind).to_equal("title")
expect(archived.archived).to_equal(true)
expect(createSessionSourceLinesModeled()).to_equal(384)  # oracle: value fixed by the spec contract
```

</details>

#### should initialize repl bridge and derive titles

- should initialize repl bridge and derive titles
- Verify: should initialize repl bridge and derive titles
- Patch initial prompt and choose CCR transport
   - Expected: result.ok is true
   - Expected: result.transport equals `ccr-v2:7`
   - Expected: onUserMessage("", "  hi\nthere  ") equals `hi there`
   - Expected: initReplBridgeSourceLinesModeled() equals `569`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should initialize repl bridge and derive titles")
step("Verify: should initialize repl bridge and derive titles")
# @req: REQ-TOOLS-BridMissFile-001
step("Patch initial prompt and choose CCR transport")
val opts = InitBridgeOptions.new("session_1", "wss://bridge", "token").withPrompt("hello world").withCcrV2(7)
val result = initReplBridge(opts)
expect(result.ok).to_equal(true)
expect(result.transport).to_equal("ccr-v2:7")
expect(result.patchedPrompt).to_contain("[bridge:session_1]")
expect(onUserMessage("", "  hi\nthere  ")).to_equal("hi there")
expect(initReplBridgeSourceLinesModeled()).to_equal(569)  # oracle: value fixed by the spec contract
```

</details>

#### should model remote bridge core retries and archive

- should model remote bridge core retries and archive
- Verify: should model remote bridge core retries and archive
- Build env-less core and exercise retry/auth/archive paths
   - Expected: core.recoverFromAuthFailure(true) is true
   - Expected: withRetry(2) equals `3`
   - Expected: fetchRemoteCredentials("jwt", "https://api", 1).ok is true
   - Expected: archiveSession("session_1", 204).status equals `archived`
   - Expected: remoteBridgeCoreSourceLinesModeled() equals `1008`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model remote bridge core retries and archive")
step("Verify: should model remote bridge core retries and archive")
# @req: REQ-TOOLS-BridMissFile-001
step("Build env-less core and exercise retry/auth/archive paths")
val params = EnvLessBridgeParams.new("session_1", "wss://bridge", "token").withRemoteCredentials("jwt", "https://api")
val core = initEnvLessBridgeCore(params)
core.rebuildTransport("manual")
core.drainFlushGate()
expect(core.recoverFromAuthFailure(true)).to_equal(true)
expect(core.flushHistory()).to_contain("credentials:remote")
expect(withRetry(2)).to_equal(3)  # oracle: value fixed by the spec contract
expect(fetchRemoteCredentials("jwt", "https://api", 1).ok).to_equal(true)
expect(archiveSession("session_1", 204).status).to_equal("archived")
expect(remoteBridgeCoreSourceLinesModeled()).to_equal(1008)  # oracle: value fixed by the spec contract
```

</details>

<details>
<summary>Advanced: should model repl bridge core reconnect and poll loop</summary>

#### should model repl bridge core reconnect and poll loop

- should model repl bridge core reconnect and poll loop
- Verify: should model repl bridge core reconnect and poll loop
- Connect, reconnect, flush, poll work, and close
   - Expected: tryReconnectInPlace(core, "token2") is true
   - Expected: polled.pollCount equals `2`
   - Expected: getOAuthToken("old", "new") equals `new`
   - Expected: handleTransportPermanentClose(core, 4090) equals `closed`
   - Expected: reconnectEnvironmentWithSession("env_1", "session_1") equals `env_1:session_1`
   - Expected: replBridgeSourceLinesModeled() equals `2406`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model repl bridge core reconnect and poll loop")
step("Verify: should model repl bridge core reconnect and poll loop")
# @req: REQ-TOOLS-BridMissFile-001
step("Connect, reconnect, flush, poll work, and close")
val params = BridgeCoreParams.new("env_1", "session_1", "token", "https://api")
val core = initBridgeCore(params)
expect(tryReconnectInPlace(core, "token2")).to_equal(true)
drainFlushGate(core)
val polled = startWorkPollLoop(core, ["work_1", "work_2"])
expect(polled.pollCount).to_equal(2)  # oracle: value fixed by the spec contract
expect(getOAuthToken("old", "new")).to_equal("new")
expect(handleTransportPermanentClose(core, 4090)).to_equal("closed")
expect(reconnectEnvironmentWithSession("env_1", "session_1")).to_equal("env_1:session_1")
expect(replBridgeSourceLinesModeled()).to_equal(2406)  # oracle: value fixed by the spec contract
```

</details>


</details>

#### should model session runner extraction and completion

- should model session runner extraction and completion
- Verify: should model session runner extraction and completion
- Sanitize IDs, summarize tools, create spawner, and finish
   - Expected: safeFilenameId("../abc") equals `___abc`
   - Expected: spawner.activities[0].summary.len() equals `66`
   - Expected: extractActivities(["a", "b"]).len() equals `2`
   - Expected: extractUserMessageText(" hi ") equals `hi`
   - Expected: spawner.done("completed") equals `completed`
   - Expected: sessionRunnerSourceLinesModeled() equals `550`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model session runner extraction and completion")
step("Verify: should model session runner extraction and completion")
# @req: REQ-TOOLS-BridMissFile-001
step("Sanitize IDs, summarize tools, create spawner, and finish")
val deps = SessionSpawnerDeps.new("token", "/repo")
val spawner = createSessionSpawner(deps)
spawner.record("tool", toolSummary("Edit", "abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz"))
expect(safeFilenameId("../abc")).to_equal("___abc")
expect(spawner.activities[0].summary.len()).to_equal(66)  # oracle: value fixed by the spec contract
expect(extractActivities(["a", "b"]).len()).to_equal(2)  # oracle: value fixed by the spec contract
expect(extractUserMessageText(" hi ")).to_equal("hi")
expect(spawner.done("completed")).to_equal("completed")
expect(sessionRunnerSourceLinesModeled()).to_equal(550)  # oracle: value fixed by the spec contract
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-BridMissFile-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4de01080e8080830c7ac35e09c8cc0873078ffb5f81f2a6b93dd801ec8a02a2e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4de01080e8080830c7ac35e09c8cc0873078ffb5f81f2a6b93dd801ec8a02a2e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4de01080e8080830c7ac35e09c8cc0873078ffb5f81f2a6b93dd801ec8a02a2e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/bridge/bridge_missing_files_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/bridge/bridge_missing_files_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/bridge/bridge_missing_files_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/bridge/bridge_missing_files_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/bridge/bridge_missing_files_spec.spl:32:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model bridge UI status rendering' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/bridge/bridge_missing_files_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model bridge UI status rendering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/bridge_missing_files_spec.spl:45:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model bridge session lifecycle' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/bridge/bridge_missing_files_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model bridge session lifecycle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/bridge_missing_files_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should initialize repl bridge and derive titles' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/bridge/bridge_missing_files_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should initialize repl bridge and derive titles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/bridge_missing_files_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model remote bridge core retries and archive' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/bridge/bridge_missing_files_spec.spl:91:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model repl bridge core reconnect and poll loop' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/bridge/bridge_missing_files_spec.spl:108:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model session runner extraction and completion' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
