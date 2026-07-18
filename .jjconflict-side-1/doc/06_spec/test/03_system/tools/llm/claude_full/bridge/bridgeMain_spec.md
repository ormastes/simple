# Claude Full Bridge Main

> Checks deterministic parity for Claude remote-control bridge startup: backoff, argument validation, retry classification, headless permanent errors, and headless logger output.

<!-- sdn-diagram:id=bridgeMain_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bridgeMain_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bridgeMain_spec -> std
bridgeMain_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bridgeMain_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge Main

Checks deterministic parity for Claude remote-control bridge startup: backoff, argument validation, retry classification, headless permanent errors, and headless logger output.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A - strict llm_caret Claude CLI parity lane. |
| Plan | N/A - target selected from strict checker output. |
| Design | N/A - source mirror for `tmp/claude/claude-code-main/src/bridge/bridgeMain.ts`. |
| Research | N/A - upstream TypeScript file is the source reference. |
| Source | `test/03_system/tools/llm/claude_full/bridge/bridgeMain_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Checks deterministic parity for Claude remote-control bridge startup: backoff,
argument validation, retry classification, headless permanent errors, and
headless logger output.

**Requirements:** N/A - strict llm_caret Claude CLI parity lane.
**Plan:** N/A - target selected from strict checker output.
**Design:** N/A - source mirror for `tmp/claude/claude-code-main/src/bridge/bridgeMain.ts`.
**Research:** N/A - upstream TypeScript file is the source reference.

## Scenarios

### Claude full bridge main

#### should expose default backoff and sleep threshold

- Read default retry values
   - Expected: backoff.connInitialMs equals `2000`
   - Expected: backoff.connCapMs equals `120000`
   - Expected: pollSleepDetectionThresholdMs(backoff) equals `240000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read default retry values")
val backoff = BackoffConfig.default()
expect(backoff.connInitialMs).to_equal(2000)
expect(backoff.connCapMs).to_equal(120000)
expect(pollSleepDetectionThresholdMs(backoff)).to_equal(240000)
```

</details>

#### should prepend script args only for npm mode

- Compare bundled and npm launch mode
   - Expected: spawnScriptArgs(true, "/cli.js").len() equals `0`
   - Expected: spawnScriptArgs(false, "/cli.js")[0] equals `/cli.js`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare bundled and npm launch mode")
expect(spawnScriptArgs(true, "/cli.js").len()).to_equal(0)
expect(spawnScriptArgs(false, "/cli.js")[0]).to_equal("/cli.js")
```

</details>

#### should classify connection and server errors

- Check retry classifiers
   - Expected: isConnectionError("ECONNRESET") is true
   - Expected: isConnectionError("ENOENT") is false
   - Expected: isServerError("ERR_BAD_RESPONSE") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check retry classifiers")
expect(isConnectionError("ECONNRESET")).to_equal(true)
expect(isConnectionError("ENOENT")).to_equal(false)
expect(isServerError("ERR_BAD_RESPONSE")).to_equal(true)
```

</details>

#### should parse spawn and capacity options

- Parse multi-session flags
   - Expected: parsed.spawnMode equals `worktree`
   - Expected: parsed.capacity equals `5`
   - Expected: parsed.name equals `desk`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse multi-session flags")
val parsed = parseArgs(["--spawn=worktree", "--capacity", "5", "--name=desk"], true)
expect(parsed.spawnMode).to_equal("worktree")
expect(parsed.capacity).to_equal(5)
expect(parsed.name).to_equal("desk")
```

</details>

#### should reject incompatible resume and spawn options

- Parse invalid resume combination


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse invalid resume combination")
val parsed = parseArgs(["--session-id=abc", "--spawn=same-dir"], true)
expect(parsed.error).to_contain("--session-id and --continue cannot be used")
```

</details>

#### should derive compact session titles

- Collapse whitespace and truncate
   - Expected: deriveSessionTitle("  hello\nworld\t") equals `hello world`
   - Expected: deriveSessionTitle("abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz").len() equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Collapse whitespace and truncate")
expect(deriveSessionTitle("  hello\nworld\t")).to_equal("hello world")
expect(deriveSessionTitle("abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz").len()).to_equal(80)
```

</details>

#### should mark headless trust failures permanent

- Run headless preflight without accepted trust
- var opts = HeadlessBridgeOpts new
   - Expected: result.ok is false
   - Expected: result.permanent is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run headless preflight without accepted trust")
var opts = HeadlessBridgeOpts.new("/repo", "same-dir", 2)
opts.trustedWorkspace = false
opts.accessToken = "token"
val result = runBridgeHeadless(opts, "", "")
expect(result.ok).to_equal(false)
expect(result.permanent).to_equal(true)
expect(result.message).to_contain("Workspace not trusted")
```

</details>

#### should keep missing auth transient for supervisor retry

- Run headless preflight without token
   - Expected: result.ok is false
   - Expected: result.permanent is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run headless preflight without token")
val opts = HeadlessBridgeOpts.new("/repo", "same-dir", 2)
val result = runBridgeHeadless(opts, "", "")
expect(result.ok).to_equal(false)
expect(result.permanent).to_equal(false)
expect(result.message).to_contain("Remote Control is only available")
```

</details>

#### should reject non-local HTTP permanently

- Run headless preflight with insecure base URL
- var opts = HeadlessBridgeOpts new
   - Expected: result.permanent is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run headless preflight with insecure base URL")
var opts = HeadlessBridgeOpts.new("/repo", "same-dir", 2)
opts.accessToken = "token"
opts.baseUrl = "http://example.com"
val result = runBridgeHeadless(opts, "", "")
expect(result.permanent).to_equal(true)
expect(result.message).to_contain("Only HTTPS or localhost HTTP")
```

</details>

#### should reject worktree mode without git or hook permanently

- Run headless preflight without worktree support
- var opts = HeadlessBridgeOpts new
   - Expected: result.permanent is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run headless preflight without worktree support")
var opts = HeadlessBridgeOpts.new("/repo", "worktree", 2)
opts.accessToken = "token"
opts.hasGitRoot = false
opts.hasWorktreeCreateHook = false
val result = runBridgeHeadless(opts, "", "")
expect(result.permanent).to_equal(true)
expect(result.message).to_contain("Worktree mode requires")
```

</details>

#### should register headless bridge and create initial session

- Run successful headless startup
- var opts = HeadlessBridgeOpts new
   - Expected: result.ok is true
   - Expected: result.environmentId equals `env-/repo`
   - Expected: result.initialSessionId equals `session_1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run successful headless startup")
var opts = HeadlessBridgeOpts.new("/repo", "same-dir", 3)
opts.accessToken = "token"
opts.createSessionOnStart = true
val result = runBridgeHeadless(opts, "", "session_1")
expect(result.ok).to_equal(true)
expect(result.environmentId).to_equal("env-/repo")
expect(result.initialSessionId).to_equal("session_1")
expect(result.logs[0]).to_contain("registered environmentId=env-/repo")
```

</details>

#### should expose source-backed class and line constants

- Pin strict checker surface
   - Expected: error.name equals `BridgeHeadlessPermanentError`
   - Expected: error.message equals `bad config`
   - Expected: bridgeMainSourceLinesModeled() equals `2999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin strict checker surface")
val error = BridgeHeadlessPermanentError.new("bad config")
expect(error.name).to_equal("BridgeHeadlessPermanentError")
expect(error.message).to_equal("bad config")
expect(bridgeMainSourceLinesModeled()).to_equal(2999)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [N/A - strict llm_caret Claude CLI parity lane.](N/A - strict llm_caret Claude CLI parity lane.)
- **Plan:** [N/A - target selected from strict checker output.](N/A - target selected from strict checker output.)
- **Design:** [N/A - source mirror for `tmp/claude/claude-code-main/src/bridge/bridgeMain.ts`.](N/A - source mirror for `tmp/claude/claude-code-main/src/bridge/bridgeMain.ts`.)
- **Research:** [N/A - upstream TypeScript file is the source reference.](N/A - upstream TypeScript file is the source reference.)


</details>
