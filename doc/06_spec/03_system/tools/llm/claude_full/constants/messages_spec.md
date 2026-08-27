# Claude Full Constants

> Purpose: should expose the no-content placeholder used by Claude output

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Constants

Purpose: should expose the no-content placeholder used by Claude output

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/constants/messages_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should expose the no-content placeholder used by Claude output
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Constants

Mirrors the smallest Claude constant-only source files so the full-parity
matrix has executable evidence for literal values, not just target paths.

## Scenarios

### Claude full constant parity

#### should expose the no-content placeholder used by Claude output

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose the no-content placeholder used by Claude output
- Verify: should expose the no-content placeholder used by Claude output
- Read the constant mapped from constants/messages.ts
   - Expected: NO_CONTENT_MESSAGE equals `(no content)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose the no-content placeholder used by Claude output")
step("Verify: should expose the no-content placeholder used by Claude output")
# @req: REQ-TOOLS-Mess-001
step("Read the constant mapped from constants/messages.ts")
expect(NO_CONTENT_MESSAGE).to_equal("(no content)")
```

</details>

#### should expose the tool-use summary error id

- should expose the tool-use summary error id
- Verify: should expose the tool-use summary error id
- Read the constant mapped from constants/errorIds.ts
   - Expected: E_TOOL_USE_SUMMARY_GENERATION_FAILED equals `344`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose the tool-use summary error id")
step("Verify: should expose the tool-use summary error id")
# @req: REQ-TOOLS-Mess-001
step("Read the constant mapped from constants/errorIds.ts")
expect(E_TOOL_USE_SUMMARY_GENERATION_FAILED).to_equal(344)  # oracle: value fixed by the spec contract
```

</details>

#### should expose turn completion verbs

- should expose turn completion verbs
- Verify: should expose turn completion verbs
- Read constants mapped from constants/turnCompletionVerbs.ts
   - Expected: turnCompletionVerbs() equals `["Baked", "Brewed", "Churned", "Cogitated", "Cooked", "Crunched", "Sautéed",... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose turn completion verbs")
step("Verify: should expose turn completion verbs")
# @req: REQ-TOOLS-Mess-001
step("Read constants mapped from constants/turnCompletionVerbs.ts")
expect(turnCompletionVerbs()).to_equal(["Baked", "Brewed", "Churned", "Cogitated", "Cooked", "Crunched", "Sautéed", "Worked"])
```

</details>

#### should expose tool limit constants

- should expose tool limit constants
- Verify: should expose tool limit constants
- Read constants mapped from constants/toolLimits.ts
   - Expected: DEFAULT_MAX_RESULT_SIZE_CHARS equals `50000`
   - Expected: MAX_TOOL_RESULT_TOKENS equals `100000`
   - Expected: BYTES_PER_TOKEN equals `4`
   - Expected: MAX_TOOL_RESULT_BYTES equals `400000`
   - Expected: MAX_TOOL_RESULTS_PER_MESSAGE_CHARS equals `200000`
   - Expected: TOOL_SUMMARY_MAX_LENGTH equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose tool limit constants")
step("Verify: should expose tool limit constants")
# @req: REQ-TOOLS-Mess-001
step("Read constants mapped from constants/toolLimits.ts")
expect(DEFAULT_MAX_RESULT_SIZE_CHARS).to_equal(50000)  # oracle: value fixed by the spec contract
expect(MAX_TOOL_RESULT_TOKENS).to_equal(100000)  # oracle: value fixed by the spec contract
expect(BYTES_PER_TOKEN).to_equal(4)  # oracle: value fixed by the spec contract
expect(MAX_TOOL_RESULT_BYTES).to_equal(400000)  # oracle: value fixed by the spec contract
expect(MAX_TOOL_RESULTS_PER_MESSAGE_CHARS).to_equal(200000)  # oracle: value fixed by the spec contract
expect(TOOL_SUMMARY_MAX_LENGTH).to_equal(50)  # oracle: value fixed by the spec contract
```

</details>

#### should expose API media limit constants

- should expose API media limit constants
- Verify: should expose API media limit constants
- Read constants mapped from constants/apiLimits.ts
   - Expected: API_IMAGE_MAX_BASE64_SIZE equals `5242880`
   - Expected: IMAGE_TARGET_RAW_SIZE equals `3932160`
   - Expected: IMAGE_MAX_WIDTH equals `2000`
   - Expected: IMAGE_MAX_HEIGHT equals `2000`
   - Expected: PDF_TARGET_RAW_SIZE equals `20971520`
   - Expected: API_PDF_MAX_PAGES equals `100`
   - Expected: PDF_EXTRACT_SIZE_THRESHOLD equals `3145728`
   - Expected: PDF_MAX_EXTRACT_SIZE equals `104857600`
   - Expected: PDF_MAX_PAGES_PER_READ equals `20`
   - Expected: PDF_AT_MENTION_INLINE_THRESHOLD equals `10`
   - Expected: API_MAX_MEDIA_PER_REQUEST equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose API media limit constants")
step("Verify: should expose API media limit constants")
# @req: REQ-TOOLS-Mess-001
step("Read constants mapped from constants/apiLimits.ts")
expect(API_IMAGE_MAX_BASE64_SIZE).to_equal(5242880)  # oracle: value fixed by the spec contract
expect(IMAGE_TARGET_RAW_SIZE).to_equal(3932160)  # oracle: value fixed by the spec contract
expect(IMAGE_MAX_WIDTH).to_equal(2000)  # oracle: value fixed by the spec contract
expect(IMAGE_MAX_HEIGHT).to_equal(2000)  # oracle: value fixed by the spec contract
expect(PDF_TARGET_RAW_SIZE).to_equal(20971520)  # oracle: value fixed by the spec contract
expect(API_PDF_MAX_PAGES).to_equal(100)  # oracle: value fixed by the spec contract
expect(PDF_EXTRACT_SIZE_THRESHOLD).to_equal(3145728)  # oracle: value fixed by the spec contract
expect(PDF_MAX_EXTRACT_SIZE).to_equal(104857600)  # oracle: value fixed by the spec contract
expect(PDF_MAX_PAGES_PER_READ).to_equal(20)  # oracle: value fixed by the spec contract
expect(PDF_AT_MENTION_INLINE_THRESHOLD).to_equal(10)  # oracle: value fixed by the spec contract
expect(API_MAX_MEDIA_PER_REQUEST).to_equal(100)  # oracle: value fixed by the spec contract
```

</details>

#### should expose beta header constants

- should expose beta header constants
- Verify: should expose beta header constants
- Read constants mapped from constants/betas.ts
   - Expected: CLAUDE_CODE_20250219_BETA_HEADER equals `claude-code-20250219`
   - Expected: INTERLEAVED_THINKING_BETA_HEADER equals `interleaved-thinking-2025-05-14`
   - Expected: CONTEXT_1M_BETA_HEADER equals `context-1m-2025-08-07`
   - Expected: CONTEXT_MANAGEMENT_BETA_HEADER equals `context-management-2025-06-27`
   - Expected: STRUCTURED_OUTPUTS_BETA_HEADER equals `structured-outputs-2025-12-15`
   - Expected: WEB_SEARCH_BETA_HEADER equals `web-search-2025-03-05`
   - Expected: TOOL_SEARCH_BETA_HEADER_1P equals `advanced-tool-use-2025-11-20`
   - Expected: TOOL_SEARCH_BETA_HEADER_3P equals `tool-search-tool-2025-10-19`
   - Expected: EFFORT_BETA_HEADER equals `effort-2025-11-24`
   - Expected: TASK_BUDGETS_BETA_HEADER equals `task-budgets-2026-03-13`
   - Expected: PROMPT_CACHING_SCOPE_BETA_HEADER equals `prompt-caching-scope-2026-01-05`
   - Expected: FAST_MODE_BETA_HEADER equals `fast-mode-2026-02-01`
   - Expected: REDACT_THINKING_BETA_HEADER equals `redact-thinking-2026-02-12`
   - Expected: TOKEN_EFFICIENT_TOOLS_BETA_HEADER equals `token-efficient-tools-2026-03-28`
   - Expected: ADVISOR_BETA_HEADER equals `advisor-tool-2026-03-01`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose beta header constants")
step("Verify: should expose beta header constants")
# @req: REQ-TOOLS-Mess-001
step("Read constants mapped from constants/betas.ts")
expect(CLAUDE_CODE_20250219_BETA_HEADER).to_equal("claude-code-20250219")
expect(INTERLEAVED_THINKING_BETA_HEADER).to_equal("interleaved-thinking-2025-05-14")
expect(CONTEXT_1M_BETA_HEADER).to_equal("context-1m-2025-08-07")
expect(CONTEXT_MANAGEMENT_BETA_HEADER).to_equal("context-management-2025-06-27")
expect(STRUCTURED_OUTPUTS_BETA_HEADER).to_equal("structured-outputs-2025-12-15")
expect(WEB_SEARCH_BETA_HEADER).to_equal("web-search-2025-03-05")
expect(TOOL_SEARCH_BETA_HEADER_1P).to_equal("advanced-tool-use-2025-11-20")
expect(TOOL_SEARCH_BETA_HEADER_3P).to_equal("tool-search-tool-2025-10-19")
expect(EFFORT_BETA_HEADER).to_equal("effort-2025-11-24")
expect(TASK_BUDGETS_BETA_HEADER).to_equal("task-budgets-2026-03-13")
expect(PROMPT_CACHING_SCOPE_BETA_HEADER).to_equal("prompt-caching-scope-2026-01-05")
expect(FAST_MODE_BETA_HEADER).to_equal("fast-mode-2026-02-01")
expect(REDACT_THINKING_BETA_HEADER).to_equal("redact-thinking-2026-02-12")
expect(TOKEN_EFFICIENT_TOOLS_BETA_HEADER).to_equal("token-efficient-tools-2026-03-28")
expect(ADVISOR_BETA_HEADER).to_equal("advisor-tool-2026-03-01")
```

</details>

#### should model feature-gated beta headers and allowed beta sets

- should model feature-gated beta headers and allowed beta sets
- Verify: should model feature-gated beta headers and allowed beta sets
- Read feature route constants mapped from constants/betas.ts
   - Expected: summarizeConnectorTextBetaHeader(true) equals `summarize-connector-text-2026-03-13`
   - Expected: summarizeConnectorTextBetaHeader(false) equals ``
   - Expected: afkModeBetaHeader(true) equals `afk-mode-2026-01-31`
   - Expected: afkModeBetaHeader(false) equals ``
   - Expected: cliInternalBetaHeader(true) equals `cli-internal-2026-02-09`
   - Expected: cliInternalBetaHeader(false) equals ``
   - Expected: bedrockExtraParamsHeaders() equals `["interleaved-thinking-2025-05-14", "context-1m-2025-08-07", "tool-search-too... (full value in folded executable source)`
   - Expected: vertexCountTokensAllowedBetas() equals `["claude-code-20250219", "interleaved-thinking-2025-05-14", "context-manageme... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model feature-gated beta headers and allowed beta sets")
step("Verify: should model feature-gated beta headers and allowed beta sets")
# @req: REQ-TOOLS-Mess-001
step("Read feature route constants mapped from constants/betas.ts")
expect(summarizeConnectorTextBetaHeader(true)).to_equal("summarize-connector-text-2026-03-13")
expect(summarizeConnectorTextBetaHeader(false)).to_equal("")
expect(afkModeBetaHeader(true)).to_equal("afk-mode-2026-01-31")
expect(afkModeBetaHeader(false)).to_equal("")
expect(cliInternalBetaHeader(true)).to_equal("cli-internal-2026-02-09")
expect(cliInternalBetaHeader(false)).to_equal("")
expect(bedrockExtraParamsHeaders()).to_equal(["interleaved-thinking-2025-05-14", "context-1m-2025-08-07", "tool-search-tool-2025-10-19"])
expect(vertexCountTokensAllowedBetas()).to_equal(["claude-code-20250219", "interleaved-thinking-2025-05-14", "context-management-2025-06-27"])
```

</details>

#### should expose XML tag constants and argument groups

- should expose XML tag constants and argument groups
- Verify: should expose XML tag constants and argument groups
- Read constants mapped from constants/xml.ts
   - Expected: COMMAND_NAME_TAG equals `command-name`
   - Expected: COMMAND_MESSAGE_TAG equals `command-message`
   - Expected: COMMAND_ARGS_TAG equals `command-args`
   - Expected: BASH_INPUT_TAG equals `bash-input`
   - Expected: BASH_STDOUT_TAG equals `bash-stdout`
   - Expected: BASH_STDERR_TAG equals `bash-stderr`
   - Expected: LOCAL_COMMAND_STDOUT_TAG equals `local-command-stdout`
   - Expected: LOCAL_COMMAND_STDERR_TAG equals `local-command-stderr`
   - Expected: LOCAL_COMMAND_CAVEAT_TAG equals `local-command-caveat`
   - Expected: TICK_TAG equals `tick`
   - Expected: TASK_NOTIFICATION_TAG equals `task-notification`
   - Expected: TASK_ID_TAG equals `task-id`
   - Expected: TOOL_USE_ID_TAG equals `tool-use-id`
   - Expected: TASK_TYPE_TAG equals `task-type`
   - Expected: OUTPUT_FILE_TAG equals `output-file`
   - Expected: STATUS_TAG equals `status`
   - Expected: SUMMARY_TAG equals `summary`
   - Expected: REASON_TAG equals `reason`
   - Expected: WORKTREE_TAG equals `worktree`
   - Expected: WORKTREE_PATH_TAG equals `worktreePath`
   - Expected: WORKTREE_BRANCH_TAG equals `worktreeBranch`
   - Expected: ULTRAPLAN_TAG equals `ultraplan`
   - Expected: REMOTE_REVIEW_TAG equals `remote-review`
   - Expected: REMOTE_REVIEW_PROGRESS_TAG equals `remote-review-progress`
   - Expected: TEAMMATE_MESSAGE_TAG equals `teammate-message`
   - Expected: CHANNEL_MESSAGE_TAG equals `channel-message`
   - Expected: CHANNEL_TAG equals `channel`
   - Expected: CROSS_SESSION_MESSAGE_TAG equals `cross-session-message`
   - Expected: FORK_BOILERPLATE_TAG equals `fork-boilerplate`
   - Expected: FORK_DIRECTIVE_PREFIX equals `Your directive: `
   - Expected: terminalOutputTags() equals `["bash-input", "bash-stdout", "bash-stderr", "local-command-stdout", "local-c... (full value in folded executable source)`
   - Expected: commonHelpArgs() equals `["help", "-h", "--help"]`
   - Expected: commonInfoArgs() equals `["list", "show", "display", "current", "view", "get", "check", "describe", "p... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose XML tag constants and argument groups")
step("Verify: should expose XML tag constants and argument groups")
# @req: REQ-TOOLS-Mess-001
step("Read constants mapped from constants/xml.ts")
expect(COMMAND_NAME_TAG).to_equal("command-name")
expect(COMMAND_MESSAGE_TAG).to_equal("command-message")
expect(COMMAND_ARGS_TAG).to_equal("command-args")
expect(BASH_INPUT_TAG).to_equal("bash-input")
expect(BASH_STDOUT_TAG).to_equal("bash-stdout")
expect(BASH_STDERR_TAG).to_equal("bash-stderr")
expect(LOCAL_COMMAND_STDOUT_TAG).to_equal("local-command-stdout")
expect(LOCAL_COMMAND_STDERR_TAG).to_equal("local-command-stderr")
expect(LOCAL_COMMAND_CAVEAT_TAG).to_equal("local-command-caveat")
expect(TICK_TAG).to_equal("tick")
expect(TASK_NOTIFICATION_TAG).to_equal("task-notification")
expect(TASK_ID_TAG).to_equal("task-id")
expect(TOOL_USE_ID_TAG).to_equal("tool-use-id")
expect(TASK_TYPE_TAG).to_equal("task-type")
expect(OUTPUT_FILE_TAG).to_equal("output-file")
expect(STATUS_TAG).to_equal("status")
expect(SUMMARY_TAG).to_equal("summary")
expect(REASON_TAG).to_equal("reason")
expect(WORKTREE_TAG).to_equal("worktree")
expect(WORKTREE_PATH_TAG).to_equal("worktreePath")
expect(WORKTREE_BRANCH_TAG).to_equal("worktreeBranch")
expect(ULTRAPLAN_TAG).to_equal("ultraplan")
expect(REMOTE_REVIEW_TAG).to_equal("remote-review")
expect(REMOTE_REVIEW_PROGRESS_TAG).to_equal("remote-review-progress")
expect(TEAMMATE_MESSAGE_TAG).to_equal("teammate-message")
expect(CHANNEL_MESSAGE_TAG).to_equal("channel-message")
expect(CHANNEL_TAG).to_equal("channel")
expect(CROSS_SESSION_MESSAGE_TAG).to_equal("cross-session-message")
expect(FORK_BOILERPLATE_TAG).to_equal("fork-boilerplate")
expect(FORK_DIRECTIVE_PREFIX).to_equal("Your directive: ")
expect(terminalOutputTags()).to_equal(["bash-input", "bash-stdout", "bash-stderr", "local-command-stdout", "local-command-stderr", "local-command-caveat"])
expect(commonHelpArgs()).to_equal(["help", "-h", "--help"])
expect(commonInfoArgs()).to_equal(["list", "show", "display", "current", "view", "get", "check", "describe", "print", "version", "about", "status", "?"])
```

</details>

#### should expose figure glyph constants

- should expose figure glyph constants
- Verify: should expose figure glyph constants
- Read constants mapped from constants/figures.ts
   - Expected: blackCircle("darwin") equals `⏺`
   - Expected: blackCircle("linux") equals `●`
   - Expected: BULLET_OPERATOR equals `∙`
   - Expected: TEARDROP_ASTERISK equals `✻`
   - Expected: UP_ARROW equals `↑`
   - Expected: DOWN_ARROW equals `↓`
   - Expected: LIGHTNING_BOLT equals `↯`
   - Expected: EFFORT_LOW equals `○`
   - Expected: EFFORT_MEDIUM equals `◐`
   - Expected: EFFORT_HIGH equals `●`
   - Expected: EFFORT_MAX equals `◉`
   - Expected: PLAY_ICON equals `▶`
   - Expected: PAUSE_ICON equals `⏸`
   - Expected: REFRESH_ARROW equals `↻`
   - Expected: CHANNEL_ARROW equals `←`
   - Expected: INJECTED_ARROW equals `→`
   - Expected: FORK_GLYPH equals `⑂`
   - Expected: DIAMOND_OPEN equals `◇`
   - Expected: DIAMOND_FILLED equals `◆`
   - Expected: REFERENCE_MARK equals `※`
   - Expected: FLAG_ICON equals `⚑`
   - Expected: BLOCKQUOTE_BAR equals `▎`
   - Expected: HEAVY_HORIZONTAL equals `━`
   - Expected: BRIDGE_READY_INDICATOR equals `·✔︎·`
   - Expected: BRIDGE_FAILED_INDICATOR equals `×`
   - Expected: bridgeSpinnerFrames() equals `["·|·", "·/·", "·—·", "·\\·"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose figure glyph constants")
step("Verify: should expose figure glyph constants")
# @req: REQ-TOOLS-Mess-001
step("Read constants mapped from constants/figures.ts")
expect(blackCircle("darwin")).to_equal("⏺")
expect(blackCircle("linux")).to_equal("●")
expect(BULLET_OPERATOR).to_equal("∙")
expect(TEARDROP_ASTERISK).to_equal("✻")
expect(UP_ARROW).to_equal("↑")
expect(DOWN_ARROW).to_equal("↓")
expect(LIGHTNING_BOLT).to_equal("↯")
expect(EFFORT_LOW).to_equal("○")
expect(EFFORT_MEDIUM).to_equal("◐")
expect(EFFORT_HIGH).to_equal("●")
expect(EFFORT_MAX).to_equal("◉")
expect(PLAY_ICON).to_equal("▶")
expect(PAUSE_ICON).to_equal("⏸")
expect(REFRESH_ARROW).to_equal("↻")
expect(CHANNEL_ARROW).to_equal("←")
expect(INJECTED_ARROW).to_equal("→")
expect(FORK_GLYPH).to_equal("⑂")
expect(DIAMOND_OPEN).to_equal("◇")
expect(DIAMOND_FILLED).to_equal("◆")
expect(REFERENCE_MARK).to_equal("※")
expect(FLAG_ICON).to_equal("⚑")
expect(BLOCKQUOTE_BAR).to_equal("▎")
expect(HEAVY_HORIZONTAL).to_equal("━")
expect(BRIDGE_READY_INDICATOR).to_equal("·✔︎·")
expect(BRIDGE_FAILED_INDICATOR).to_equal("×")
expect(bridgeSpinnerFrames()).to_equal(["·|·", "·/·", "·—·", "·\\·"])
```

</details>

#### should model binary file constants

- should model binary file constants
- Verify: should model binary file constants
- Read constants mapped from constants/files.ts
   - Expected: binaryExtensions().len() equals `94`
   - Expected: hasBinaryExtension("photo.PNG") is true
   - Expected: hasBinaryExtension("archive.tar.gz") is true
   - Expected: hasBinaryExtension("notes.txt") is false
   - Expected: hasBinaryExtension("Makefile") is false
   - Expected: BINARY_CHECK_SIZE equals `8192`
   - Expected: isBinaryContentBytes([65, 66, 67, 10]) is false
   - Expected: isBinaryContentBytes([65, 0, 67]) is true
   - Expected: isBinaryContentBytes([1, 2, 3, 4, 5, 65, 66, 67, 68, 69]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model binary file constants")
step("Verify: should model binary file constants")
# @req: REQ-TOOLS-Mess-001
step("Read constants mapped from constants/files.ts")
expect(binaryExtensions().len()).to_equal(94)  # oracle: value fixed by the spec contract
expect(hasBinaryExtension("photo.PNG")).to_equal(true)
expect(hasBinaryExtension("archive.tar.gz")).to_equal(true)
expect(hasBinaryExtension("notes.txt")).to_equal(false)
expect(hasBinaryExtension("Makefile")).to_equal(false)
expect(BINARY_CHECK_SIZE).to_equal(8192)  # oracle: value fixed by the spec contract
expect(isBinaryContentBytes([65, 66, 67, 10])).to_equal(false)
expect(isBinaryContentBytes([65, 0, 67])).to_equal(true)
expect(isBinaryContentBytes([1, 2, 3, 4, 5, 65, 66, 67, 68, 69])).to_equal(true)
```

</details>

#### should model GrowthBook client key routing

- should model GrowthBook client key routing
- Verify: should model GrowthBook client key routing
- Read route mapped from constants/keys.ts
   - Expected: growthBookClientKey(true, true) equals `sdk-yZQvlplybuXjYh6L`
   - Expected: growthBookClientKey(true, false) equals `sdk-xRVcrliHIlrg4og4`
   - Expected: growthBookClientKey(false, true) equals `sdk-zAZezfDKGoZuXXKe`
   - Expected: growthBookClientKey(false, false) equals `sdk-zAZezfDKGoZuXXKe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model GrowthBook client key routing")
step("Verify: should model GrowthBook client key routing")
# @req: REQ-TOOLS-Mess-001
step("Read route mapped from constants/keys.ts")
expect(growthBookClientKey(true, true)).to_equal("sdk-yZQvlplybuXjYh6L")
expect(growthBookClientKey(true, false)).to_equal("sdk-xRVcrliHIlrg4og4")
expect(growthBookClientKey(false, true)).to_equal("sdk-zAZezfDKGoZuXXKe")
expect(growthBookClientKey(false, false)).to_equal("sdk-zAZezfDKGoZuXXKe")
```

</details>

#### should model Claude product URLs

- should model Claude product URLs
- Verify: should model Claude product URLs
- Read routes mapped from constants/product.ts
   - Expected: PRODUCT_URL equals `https://claude.com/claude-code`
   - Expected: CLAUDE_AI_BASE_URL equals `https://claude.ai`
   - Expected: CLAUDE_AI_STAGING_BASE_URL equals `https://claude-ai.staging.ant.dev`
   - Expected: CLAUDE_AI_LOCAL_BASE_URL equals `http://localhost:4000`
   - Expected: isRemoteSessionStaging("session_staging_abc", "") is true
   - Expected: isRemoteSessionStaging("session_abc", "https://claude-ai.staging.ant.dev") is true
   - Expected: isRemoteSessionLocal("session_local_abc", "") is true
   - Expected: isRemoteSessionLocal("session_abc", "http://localhost:4000") is true
   - Expected: getClaudeAiBaseUrl("session_local_abc", "") equals `http://localhost:4000`
   - Expected: getClaudeAiBaseUrl("session_staging_abc", "") equals `https://claude-ai.staging.ant.dev`
   - Expected: getClaudeAiBaseUrl("session_prod_abc", "") equals `https://claude.ai`
   - Expected: getRemoteSessionUrl("cse_abc", "") equals `https://claude.ai/code/session_abc`
   - Expected: getRemoteSessionUrl("cse_local_abc", "") equals `http://localhost:4000/code/session_local_abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model Claude product URLs")
step("Verify: should model Claude product URLs")
# @req: REQ-TOOLS-Mess-001
step("Read routes mapped from constants/product.ts")
expect(PRODUCT_URL).to_equal("https://claude.com/claude-code")
expect(CLAUDE_AI_BASE_URL).to_equal("https://claude.ai")
expect(CLAUDE_AI_STAGING_BASE_URL).to_equal("https://claude-ai.staging.ant.dev")
expect(CLAUDE_AI_LOCAL_BASE_URL).to_equal("http://localhost:4000")
expect(isRemoteSessionStaging("session_staging_abc", "")).to_equal(true)
expect(isRemoteSessionStaging("session_abc", "https://claude-ai.staging.ant.dev")).to_equal(true)
expect(isRemoteSessionLocal("session_local_abc", "")).to_equal(true)
expect(isRemoteSessionLocal("session_abc", "http://localhost:4000")).to_equal(true)
expect(getClaudeAiBaseUrl("session_local_abc", "")).to_equal("http://localhost:4000")
expect(getClaudeAiBaseUrl("session_staging_abc", "")).to_equal("https://claude-ai.staging.ant.dev")
expect(getClaudeAiBaseUrl("session_prod_abc", "")).to_equal("https://claude.ai")
expect(getRemoteSessionUrl("cse_abc", "")).to_equal("https://claude.ai/code/session_abc")
expect(getRemoteSessionUrl("cse_local_abc", "")).to_equal("http://localhost:4000/code/session_local_abc")
```

</details>

#### should expose the Config tool name literal

- should expose the Config tool name literal
- Verify: should expose the Config tool name literal
- Read the constant mapped from tools/ConfigTool/constants.ts
   - Expected: CONFIG_TOOL_NAME equals `Config`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose the Config tool name literal")
step("Verify: should expose the Config tool name literal")
# @req: REQ-TOOLS-Mess-001
step("Read the constant mapped from tools/ConfigTool/constants.ts")
expect(CONFIG_TOOL_NAME).to_equal("Config")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Mess-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ca242afb325b759bb31778b22c9878b6ee67b3b61b2b728b3445534f3847372b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca242afb325b759bb31778b22c9878b6ee67b3b61b2b728b3445534f3847372b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca242afb325b759bb31778b22c9878b6ee67b3b61b2b728b3445534f3847372b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/constants/messages_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/constants/messages_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/constants/messages_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/constants/messages_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/constants/messages_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose the no-content placeholder used by Claude output' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/constants/messages_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose the no-content placeholder used by Claude output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/constants/messages_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose the tool-use summary error id' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/constants/messages_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose the tool-use summary error id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/constants/messages_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose turn completion verbs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/constants/messages_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose turn completion verbs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/constants/messages_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose tool limit constants' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/constants/messages_spec.spl:73:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose API media limit constants' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/constants/messages_spec.spl:91:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose beta header constants' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
