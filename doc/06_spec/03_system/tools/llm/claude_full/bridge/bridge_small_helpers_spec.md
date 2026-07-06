# Claude Full Bridge Small Helpers

> Checks the small bridge and grouped-message parity helpers added from the Claude CLI source mirror.

<!-- sdn-diagram:id=bridge_small_helpers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bridge_small_helpers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bridge_small_helpers_spec -> std
bridge_small_helpers_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bridge_small_helpers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge Small Helpers

Checks the small bridge and grouped-message parity helpers added from the Claude CLI source mirror.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A - strict llm_caret Claude CLI parity lane. |
| Plan | N/A - target selected from strict checker output. |
| Design | N/A - source mirror for Claude CLI bridge and message helpers. |
| Research | N/A - upstream TypeScript files are the source reference. |
| Source | `test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Checks the small bridge and grouped-message parity helpers added from the
Claude CLI source mirror.

## Syntax

Run with:

```bash
bin/simple test test/03_system/tools/llm/claude_full/bridge/bridge_small_helpers_spec.spl --mode=interpreter
```

## Examples

The scenarios exercise capacity wake cleanup and aborts, inbound image block
normalization, bridge polling defaults, bridge status helpers, code-session
request/response helpers, null-rendering attachments, grouped tool-use
rendering state, debug message formatting, and source line parity helpers.

**Requirements:** N/A - strict llm_caret Claude CLI parity lane.
**Plan:** N/A - target selected from strict checker output.
**Design:** N/A - source mirror for Claude CLI bridge and message helpers.
**Research:** N/A - upstream TypeScript files are the source reference.

## Scenarios

### Claude full bridge small helpers

#### should model capacity wake signal lifecycle

- Create signal, cleanup it, wake next generation, and abort
   - Expected: signal.aborted is false
   - Expected: capacityWakeCleanup(signal) is true
   - Expected: next.generation equals `1`
   - Expected: outer.aborted is true
   - Expected: outer.cleanup_needed is false
   - Expected: current.aborted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create signal, cleanup it, wake next generation, and abort")
val initial = capacityWakeInitial()
val signal = capacityWakeSignal(initial)
expect(signal.aborted).to_equal(false)
expect(capacityWakeCleanup(signal)).to_equal(true)
val next = capacityWakeWake(initial)
expect(next.generation).to_equal(1)
val outer = capacityWakeSignal(capacityWakeAbortOuter(next))
expect(outer.aborted).to_equal(true)
expect(outer.cleanup_needed).to_equal(false)
val current = capacityWakeSignal(capacityWakeAbortCurrent(next))
expect(current.aborted).to_equal(true)
```

</details>

#### should gate bridge availability with explicit entitlement inputs

- Return enabled state and disabled reasons without hidden config reads
   - Expected: isBridgeEnabled(enabled) is true
   - Expected: isBridgeEnabledBlocking(enabled) is true
   - Expected: getBridgeDisabledReason(enabled) equals ``
   - Expected: getBridgeDisabledReason(BridgeEntitlement.new(false, true, true, true, "org")) equals `Remote Control is not available in this build.`
   - Expected: getBridgeDisabledReason(BridgeEntitlement.new(true, false, true, true, "org")) equals `Remote Control requires a claude.ai subscription. Run `claude auth login` to ... (full value in folded executable source)`
   - Expected: getBridgeDisabledReason(BridgeEntitlement.new(true, true, true, false, "org")) equals `Remote Control requires a full-scope login token. Long-lived tokens (from `cl... (full value in folded executable source)`
   - Expected: getBridgeDisabledReason(BridgeEntitlement.new(true, true, true, true, "")) equals `Unable to determine your organization for Remote Control eligibility. Run `cl... (full value in folded executable source)`
   - Expected: getBridgeDisabledReason(BridgeEntitlement.new(true, true, false, true, "org")) equals `Remote Control is not yet enabled for your account.`
- var flags = BridgeFeatureFlags new
   - Expected: isEnvLessBridgeEnabled(flags) is true
   - Expected: isCseShimEnabled(flags) is true
   - Expected: checkBridgeMinVersion("1.0.0", "2.0.0", true) equals `Your version of Claude Code (1.0.0) is too old for Remote Control.\nVersion 2... (full value in folded executable source)`
   - Expected: getCcrAutoConnectDefault(true, true) is true
   - Expected: isCcrMirrorEnabled(flags) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Return enabled state and disabled reasons without hidden config reads")
val enabled = BridgeEntitlement.new(true, true, true, true, "org")
expect(isBridgeEnabled(enabled)).to_equal(true)
expect(isBridgeEnabledBlocking(enabled)).to_equal(true)
expect(getBridgeDisabledReason(enabled)).to_equal("")
expect(getBridgeDisabledReason(BridgeEntitlement.new(false, true, true, true, "org"))).to_equal("Remote Control is not available in this build.")
expect(getBridgeDisabledReason(BridgeEntitlement.new(true, false, true, true, "org"))).to_equal("Remote Control requires a claude.ai subscription. Run `claude auth login` to sign in with your claude.ai account.")
expect(getBridgeDisabledReason(BridgeEntitlement.new(true, true, true, false, "org"))).to_equal("Remote Control requires a full-scope login token. Long-lived tokens (from `claude setup-token` or CLAUDE_CODE_OAUTH_TOKEN) are limited to inference-only for security reasons. Run `claude auth login` to use Remote Control.")
expect(getBridgeDisabledReason(BridgeEntitlement.new(true, true, true, true, ""))).to_equal("Unable to determine your organization for Remote Control eligibility. Run `claude auth login` to refresh your account information.")
expect(getBridgeDisabledReason(BridgeEntitlement.new(true, true, false, true, "org"))).to_equal("Remote Control is not yet enabled for your account.")
var flags = BridgeFeatureFlags.new()
flags.env_less_bridge = true
expect(isEnvLessBridgeEnabled(flags)).to_equal(true)
expect(isCseShimEnabled(flags)).to_equal(true)
expect(checkBridgeMinVersion("1.0.0", "2.0.0", true)).to_equal("Your version of Claude Code (1.0.0) is too old for Remote Control.\nVersion 2.0.0 or higher is required. Run `claude update` to update.")
expect(getCcrAutoConnectDefault(true, true)).to_equal(true)
flags.ccr_mirror_build = true
flags.ccr_mirror_env = true
expect(isCcrMirrorEnabled(flags)).to_equal(true)
```

</details>

#### should validate env-less bridge config

- Use defaults, reject invalid timing floors, and apply upgrade nudges
   - Expected: defaults.init_retry_max_attempts equals `3`
   - Expected: defaults.http_timeout_ms equals `10000`
   - Expected: validateEnvLessBridgeConfig(defaults) is true
   - Expected: validateEnvLessBridgeConfig(invalid) is false
   - Expected: getEnvLessBridgeConfig(false, invalid).heartbeat_interval_ms equals `20000`
   - Expected: checkEnvLessBridgeMinVersion("1.0.0", defaults) equals ``
   - Expected: checkEnvLessBridgeMinVersion("1.0.0", upgrade) equals `Your version of Claude Code (1.0.0) is too old for Remote Control.\nVersion 2... (full value in folded executable source)`
   - Expected: shouldShowAppUpgradeMessage(false, upgrade) is false
   - Expected: shouldShowAppUpgradeMessage(true, upgrade) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use defaults, reject invalid timing floors, and apply upgrade nudges")
val defaults = EnvLessBridgeConfig.defaults()
expect(defaults.init_retry_max_attempts).to_equal(3)
expect(defaults.http_timeout_ms).to_equal(10000)
expect(validateEnvLessBridgeConfig(defaults)).to_equal(true)
var invalid = defaults
invalid.heartbeat_interval_ms = 1000
expect(validateEnvLessBridgeConfig(invalid)).to_equal(false)
expect(getEnvLessBridgeConfig(false, invalid).heartbeat_interval_ms).to_equal(20000)
expect(checkEnvLessBridgeMinVersion("1.0.0", defaults)).to_equal("")
var upgrade = defaults
upgrade.min_version = "2.0.0"
upgrade.should_show_app_upgrade_message = true
expect(checkEnvLessBridgeMinVersion("1.0.0", upgrade)).to_equal("Your version of Claude Code (1.0.0) is too old for Remote Control.\nVersion 2.0.0 or higher is required. Run `claude update` to update.")
expect(shouldShowAppUpgradeMessage(false, upgrade)).to_equal(false)
expect(shouldShowAppUpgradeMessage(true, upgrade)).to_equal(true)
```

</details>

#### should normalize inbound user message images

- Convert malformed camel mediaType blocks and reject empty/non-user messages
   - Expected: extracted.present is true
   - Expected: extracted.blocks[0].media_type equals `image/jpeg`
   - Expected: extracted.blocks[1].media_type equals `image/png`
   - Expected: extractInboundMessageFields(InboundMessage.text("u2", "")).present is false
- var assistant = InboundMessage text
   - Expected: extractInboundMessageFields(assistant).present is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Convert malformed camel mediaType blocks and reject empty/non-user messages")
val jpeg = InboundContentBlock.imageBlock("", "", "/9j/base64")
val png = InboundContentBlock.imageBlock("", "image/png", "iVBORbase64")
val extracted = extractInboundMessageFields(InboundMessage.block("u1", [jpeg, png]))
expect(extracted.present).to_equal(true)
expect(extracted.blocks[0].media_type).to_equal("image/jpeg")
expect(extracted.blocks[1].media_type).to_equal("image/png")
expect(extractInboundMessageFields(InboundMessage.text("u2", "")).present).to_equal(false)
var assistant = InboundMessage.text("a1", "hello")
assistant.type_name = "assistant"
expect(extractInboundMessageFields(assistant).present).to_equal(false)
```

</details>

#### should resolve and prepend inbound attachments

- Filter valid attachments, sanitize names, and add path refs
   - Expected: extractInboundAttachments(msg).len() equals `1`
   - Expected: sanitizeInboundAttachmentFileName("../notes bad.md") equals `notes_bad.md`
   - Expected: prefix equals `@"/cfg/uploads/sess/abc12345-notes_bad.md" `
   - Expected: resolveAndPrependInboundAttachmentText(msg, "open", ctx) equals `@"/cfg/uploads/sess/abc12345-notes_bad.md" open`
   - Expected: blocks[1].text_value equals `@"/cfg/uploads/sess/abc12345-notes_bad.md" body`
   - Expected: resolveInboundAttachments([attachment], noToken) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Filter valid attachments, sanitize names, and add path refs")
val attachment = InboundAttachment.new("abc123456789", "../notes bad.md")
val msg = InboundAttachmentMessage.withAttachments([attachment, InboundAttachment.new("", "skip")])
expect(extractInboundAttachments(msg).len()).to_equal(1)
expect(sanitizeInboundAttachmentFileName("../notes bad.md")).to_equal("notes_bad.md")
val ctx = InboundAttachmentContext.ok("tok", "https://api", "/cfg", "sess")
val prefix = resolveInboundAttachments(extractInboundAttachments(msg), ctx)
expect(prefix).to_equal("@\"/cfg/uploads/sess/abc12345-notes_bad.md\" ")
expect(resolveAndPrependInboundAttachmentText(msg, "open", ctx)).to_equal("@\"/cfg/uploads/sess/abc12345-notes_bad.md\" open")
val blocks = prependPathRefsToBlocks([InboundAttachmentContentBlock.nonText("image"), InboundAttachmentContentBlock.textBlock("body")], prefix)
expect(blocks[1].text_value).to_equal("@\"/cfg/uploads/sess/abc12345-notes_bad.md\" body")
var noToken = ctx
noToken.access_token = ""
expect(resolveInboundAttachments([attachment], noToken)).to_equal("")
```

</details>

#### should expose bridge poll defaults

- Read default intervals and boolean helpers
   - Expected: cfg.poll_interval_ms_not_at_capacity equals `2000`
   - Expected: cfg.poll_interval_ms_at_capacity equals `600000`
   - Expected: pollConfigAtCapacityDisabled(cfg) is false
   - Expected: pollConfigHeartbeatEnabled(cfg) is false
   - Expected: pollConfigKeepaliveEnabled(cfg) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read default intervals and boolean helpers")
val cfg = defaultPollConfig()
expect(cfg.poll_interval_ms_not_at_capacity).to_equal(2000)
expect(cfg.poll_interval_ms_at_capacity).to_equal(600000)
expect(pollConfigAtCapacityDisabled(cfg)).to_equal(false)
expect(pollConfigHeartbeatEnabled(cfg)).to_equal(false)
expect(pollConfigKeepaliveEnabled(cfg)).to_equal(true)
```

</details>

#### should render grouped tool-use state

- Hide without renderer, animate in-progress groups, and match result ids
   - Expected: hidden.visible is false
   - Expected: render.visible is true
   - Expected: render.tool_name equals `Bash`
   - Expected: render.should_animate is true
   - Expected: render.item_count equals `2`
   - Expected: groupedToolUseResultFor("a", ["x", "a"]) is true
   - Expected: groupedToolUseResultFor("z", ["x", "a"]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Hide without renderer, animate in-progress groups, and match result ids")
val done = GroupedToolUseItem.new("a", true, false, false, 0, true)
val running = GroupedToolUseItem.new("b", false, false, true, 2, false)
val hidden = groupedToolUseContent("Bash", false, [done], true)
expect(hidden.visible).to_equal(false)
val render = groupedToolUseContent("Bash", true, [done, running], true)
expect(render.visible).to_equal(true)
expect(render.tool_name).to_equal("Bash")
expect(render.should_animate).to_equal(true)
expect(render.item_count).to_equal(2)
expect(groupedToolUseResultFor("a", ["x", "a"])).to_equal(true)
expect(groupedToolUseResultFor("z", ["x", "a"])).to_equal(false)
```

</details>

#### should render hook progress state

- Hide completed or non-transcript tool hooks and render running hooks
   - Expected: hookProgressMessage(HookProgressMessageInput.new("PreToolUse", 1, 0, false)).visible is false
   - Expected: transcript.visible is true
   - Expected: hookProgressMessageLine(transcript) equals `2 PostToolUse hooks ran`
   - Expected: hookProgressMessage(HookProgressMessageInput.new("Notification", 2, 2, false)).visible is false
   - Expected: running.mode equals `running`
   - Expected: hookProgressMessageLine(running) equals `Running Notification hook...`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Hide completed or non-transcript tool hooks and render running hooks")
expect(hookProgressMessage(HookProgressMessageInput.new("PreToolUse", 1, 0, false)).visible).to_equal(false)
val transcript = hookProgressMessage(HookProgressMessageInput.new("PostToolUse", 2, 0, true))
expect(transcript.visible).to_equal(true)
expect(hookProgressMessageLine(transcript)).to_equal("2 PostToolUse hooks ran")
expect(hookProgressMessage(HookProgressMessageInput.new("Notification", 2, 2, false)).visible).to_equal(false)
val running = hookProgressMessage(HookProgressMessageInput.new("Notification", 1, 0, false))
expect(running.mode).to_equal("running")
expect(hookProgressMessageLine(running)).to_equal("Running Notification hook...")
```

</details>

#### should highlight thinking trigger text

- Render brief user text and rainbow ultrathink spans
   - Expected: brief.layout equals `brief`
   - Expected: brief.label equals `You`
   - Expected: brief.timestamp equals `10:00`
   - Expected: normal.pointer equals `"❯")`
   - Expected: normal.pointer_color equals `suggestion`
   - Expected: triggers.len() equals `1`
   - Expected: triggers[0].word equals `ultrathink`
   - Expected: highlightedThinkingRainbowColor(8) equals `rainbow_orange`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render brief user text and rainbow ultrathink spans")
val brief = highlightedThinkingText("think", true, "10:00", false, false, true)
expect(brief.layout).to_equal("brief")
expect(brief.label).to_equal("You")
expect(brief.timestamp).to_equal("10:00")
val normal = highlightedThinkingText("please ultrathink now", false, "", false, true, true)
expect(normal.pointer).to_equal("❯")
expect(normal.pointer_color).to_equal("suggestion")
val triggers = findHighlightedThinkingTriggerPositions("please ultrathink now", true)
expect(triggers.len()).to_equal(1)
expect(triggers[0].word).to_equal("ultrathink")
expect(highlightedThinkingRainbowColor(8)).to_equal("rainbow_orange")
```

</details>

#### should compute bridge status utility values

- Build URLs, shimmer segments, footer labels, and OSC8 links
   - Expected: abbreviateActivity("123456789012345678901234567890XYZ") equals `123456789012345678901234567890`
   - Expected: buildBridgeConnectUrl("env1", "https://claude.example") equals `https://claude.example/code?bridge=env1`
   - Expected: buildBridgeSessionUrl("cse_abc", "env1", "https://claude.example") equals `https://claude.example/chat/session_abc?bridge=env1`
   - Expected: computeGlimmerIndex(1, 10) equals `19`
   - Expected: segments.before equals `a`
   - Expected: segments.shimmer equals `bcd`
   - Expected: segments.after_text equals `ef`
   - Expected: getBridgeStatus("", false, true, false).label equals `Remote Control active`
   - Expected: getBridgeStatus("bad", true, true, false).color equals `error`
   - Expected: buildIdleFooterText("u") equals `Code everywhere with the Claude app or u`
   - Expected: buildActiveFooterText("u") equals `Continue coding in the Claude app or u`
   - Expected: wrapWithOsc8Link("open", "https://x") equals `\u001b]8;;https://x\u0007open\u001b]8;;\u0007`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build URLs, shimmer segments, footer labels, and OSC8 links")
expect(abbreviateActivity("123456789012345678901234567890XYZ")).to_equal("123456789012345678901234567890")
expect(buildBridgeConnectUrl("env1", "https://claude.example")).to_equal("https://claude.example/code?bridge=env1")
expect(buildBridgeSessionUrl("cse_abc", "env1", "https://claude.example")).to_equal("https://claude.example/chat/session_abc?bridge=env1")
expect(computeGlimmerIndex(1, 10)).to_equal(19)
val segments = computeShimmerSegments("abcdef", 2)
expect(segments.before).to_equal("a")
expect(segments.shimmer).to_equal("bcd")
expect(segments.after_text).to_equal("ef")
expect(getBridgeStatus("", false, true, false).label).to_equal("Remote Control active")
expect(getBridgeStatus("bad", true, true, false).color).to_equal("error")
expect(buildIdleFooterText("u")).to_equal("Code everywhere with the Claude app or u")
expect(buildActiveFooterText("u")).to_equal("Continue coding in the Claude app or u")
expect(wrapWithOsc8Link("open", "https://x")).to_equal("\u001b]8;;https://x\u0007open\u001b]8;;\u0007")
```

</details>

#### should model code-session request and response validation

- Build headers, session create payloads, bridge URLs, and credential validation
   - Expected: headers.authorization equals `Bearer tok`
   - Expected: headers.anthropic_version equals `2023-06-01`
   - Expected: bridgeOauthHeaders("tok", "device").trusted_device_token equals `device`
   - Expected: request.url equals `https://api/v1/code/sessions`
   - Expected: request.bridge is true
   - Expected: createCodeSessionFromResponse(CodeSessionResponse.new(201, "cse_ok", "")) equals `cse_ok`
   - Expected: createCodeSessionFromResponse(CodeSessionResponse.new(200, "session_bad", "")) equals ``
   - Expected: codeSessionFailureLog(403, "denied") equals `[code-session] Session create failed 403: denied`
   - Expected: remoteCredentialsUrl("https://api", "cse_ok") equals `https://api/v1/code/sessions/cse_ok/bridge`
   - Expected: parseRemoteCredentials("jwt", "https://worker", 60, 2).valid is true
   - Expected: parseRemoteCredentials("", "https://worker", 60, 2).valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build headers, session create payloads, bridge URLs, and credential validation")
val headers = oauthHeaders("tok")
expect(headers.authorization).to_equal("Bearer tok")
expect(headers.anthropic_version).to_equal("2023-06-01")
expect(bridgeOauthHeaders("tok", "device").trusted_device_token).to_equal("device")
val request = createCodeSessionRequest("https://api", "title", 10, ["tag"])
expect(request.url).to_equal("https://api/v1/code/sessions")
expect(request.bridge).to_equal(true)
expect(createCodeSessionFromResponse(CodeSessionResponse.new(201, "cse_ok", ""))).to_equal("cse_ok")
expect(createCodeSessionFromResponse(CodeSessionResponse.new(200, "session_bad", ""))).to_equal("")
expect(codeSessionFailureLog(403, "denied")).to_equal("[code-session] Session create failed 403: denied")
expect(remoteCredentialsUrl("https://api", "cse_ok")).to_equal("https://api/v1/code/sessions/cse_ok/bridge")
expect(parseRemoteCredentials("jwt", "https://worker", 60, 2).valid).to_equal(true)
expect(parseRemoteCredentials("", "https://worker", 60, 2).valid).to_equal(false)
```

</details>

#### should identify null-rendering attachments

- Filter invisible attachment messages before render counting
   - Expected: isNullRenderingAttachmentType("hook_success") is true
   - Expected: isNullRenderingAttachmentType("date_change") is true
   - Expected: isNullRenderingAttachmentType("image") is false
   - Expected: isNullRenderingAttachment(NullRenderingMessage.new("attachment", "hook_cancelled")) is true
   - Expected: isNullRenderingAttachment(NullRenderingMessage.new("user", "hook_cancelled")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Filter invisible attachment messages before render counting")
expect(isNullRenderingAttachmentType("hook_success")).to_equal(true)
expect(isNullRenderingAttachmentType("date_change")).to_equal(true)
expect(isNullRenderingAttachmentType("image")).to_equal(false)
expect(isNullRenderingAttachment(NullRenderingMessage.new("attachment", "hook_cancelled"))).to_equal(true)
expect(isNullRenderingAttachment(NullRenderingMessage.new("user", "hook_cancelled"))).to_equal(false)
```

</details>

#### should list hidden model-visible features

- Pin every upstream isMeta/metaMessages surface hidden from users but sent to the model
   - Expected: features.len() equals `6`
   - Expected: hiddenModelVisibleFeatureNames() equals `[`
   - Expected: features[i].user_visible is false
   - Expected: features[i].model_visible is true
   - Expected: isHiddenModelVisibleFeature(features[i].name) is true
   - Expected: isHiddenModelVisibleFeature("ordinary-user-message") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin every upstream isMeta/metaMessages surface hidden from users but sent to the model")
val features = hiddenModelVisibleFeatures()
expect(features.len()).to_equal(6)
expect(hiddenModelVisibleFeatureNames()).to_equal([
    "queued-input-isMeta",
    "command-metaMessages",
    "slash-command-hidden-reentry",
    "image-metadata-isMeta",
    "scheduled-task-isMeta",
    "context-collapse-marker",
])
var i = 0
while i < features.len():
    expect(features[i].user_visible).to_equal(false)
    expect(features[i].model_visible).to_equal(true)
    expect(isHiddenModelVisibleFeature(features[i].name)).to_equal(true)
    i = i + 1
expect(isHiddenModelVisibleFeature("ordinary-user-message")).to_equal(false)
```

</details>

#### should format rate-limit upsell state

- Select upsell copy and auto-open callback state from explicit inputs
   - Expected: getUpsellMessage(RateLimitUpsellParams.new(false, false, false, false, false, false)) equals ``
   - Expected: getUpsellMessage(RateLimitUpsellParams.new(true, true, true, false, false, false)) equals `/extra-usage to finish what you're working on.`
   - Expected: getUpsellMessage(RateLimitUpsellParams.new(true, false, false, false, false, false)) equals `/upgrade to increase your usage limit.`
   - Expected: getUpsellMessage(RateLimitUpsellParams.new(true, false, true, false, true, false)) equals `/extra-usage to request more usage from your admin.`
   - Expected: render.errorText equals `limit hit`
   - Expected: render.shouldCallOpenRateLimitOptions is true
   - Expected: render.nextHasOpenedInteractiveMenu is true
   - Expected: rateLimitMessageAfterEffect(inputs).hasOpenedInteractiveMenu is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Select upsell copy and auto-open callback state from explicit inputs")
expect(getUpsellMessage(RateLimitUpsellParams.new(false, false, false, false, false, false))).to_equal("")
expect(getUpsellMessage(RateLimitUpsellParams.new(true, true, true, false, false, false))).to_equal("/extra-usage to finish what you're working on.")
expect(getUpsellMessage(RateLimitUpsellParams.new(true, false, false, false, false, false))).to_equal("/upgrade to increase your usage limit.")
expect(getUpsellMessage(RateLimitUpsellParams.new(true, false, true, false, true, false))).to_equal("/extra-usage to request more usage from your admin.")
val inputs = RateLimitMessageInputs.new("limit hit", "team", "tier", false, true, true, true, false, true, ClaudeAiRateLimitState.new("rejected", "soon", false))
val render = RateLimitMessage(inputs)
expect(render.errorText).to_equal("limit hit")
expect(render.shouldCallOpenRateLimitOptions).to_equal(true)
expect(render.nextHasOpenedInteractiveMenu).to_equal(true)
expect(rateLimitMessageAfterEffect(inputs).hasOpenedInteractiveMenu).to_equal(true)
```

</details>

#### should summarize task assignment messages

- Render task assignment border content and summary text
   - Expected: render.visible is true
   - Expected: render.header equals `Task #42 assigned by Ada`
   - Expected: render.subject equals `Fix parity`
   - Expected: render.description equals `Use Simple`
   - Expected: render.border_color equals `cyan_FOR_SUBAGENTS_ONLY`
   - Expected: getTaskAssignmentSummary("task:42|Ada|Fix parity|Use Simple") equals `[Task Assigned] #42 - Fix parity`
   - Expected: tryRenderTaskAssignmentMessage("plain").visible is false
   - Expected: getTaskAssignmentSummary("plain") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render task assignment border content and summary text")
val render = tryRenderTaskAssignmentMessage("task:42|Ada|Fix parity|Use Simple")
expect(render.visible).to_equal(true)
expect(render.header).to_equal("Task #42 assigned by Ada")
expect(render.subject).to_equal("Fix parity")
expect(render.description).to_equal("Use Simple")
expect(render.border_color).to_equal("cyan_FOR_SUBAGENTS_ONLY")
expect(getTaskAssignmentSummary("task:42|Ada|Fix parity|Use Simple")).to_equal("[Task Assigned] #42 - Fix parity")
expect(tryRenderTaskAssignmentMessage("plain").visible).to_equal(false)
expect(getTaskAssignmentSummary("plain")).to_equal("")
```

</details>

#### should summarize shutdown messages

- Render requests/rejections while approved messages stay caller-handled
   - Expected: request.visible is true
   - Expected: request.title equals `Shutdown request from Ada`
   - Expected: request.reason_line equals `Reason: Need deploy`
   - Expected: request.border_color equals `warning`
   - Expected: getShutdownMessageSummary("shutdown-request:Ada|Need deploy") equals `[Shutdown Request from Ada] Need deploy`
   - Expected: tryRenderShutdownMessage("shutdown-approved:Ada").visible is false
   - Expected: getShutdownMessageSummary("shutdown-approved:Ada") equals `[Shutdown Approved] Ada is now exiting`
   - Expected: rejected.visible is true
   - Expected: rejected.border_color equals `subtle`
   - Expected: rejected.footer equals `Teammate is continuing to work. You may request shutdown again later.`
   - Expected: getShutdownMessageSummary("shutdown-rejected:Grace|Still running") equals `[Shutdown Rejected] Grace: Still running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render requests/rejections while approved messages stay caller-handled")
val request = tryRenderShutdownMessage("shutdown-request:Ada|Need deploy")
expect(request.visible).to_equal(true)
expect(request.title).to_equal("Shutdown request from Ada")
expect(request.reason_line).to_equal("Reason: Need deploy")
expect(request.border_color).to_equal("warning")
expect(getShutdownMessageSummary("shutdown-request:Ada|Need deploy")).to_equal("[Shutdown Request from Ada] Need deploy")
expect(tryRenderShutdownMessage("shutdown-approved:Ada").visible).to_equal(false)
expect(getShutdownMessageSummary("shutdown-approved:Ada")).to_equal("[Shutdown Approved] Ada is now exiting")
val rejected = tryRenderShutdownMessage("shutdown-rejected:Grace|Still running")
expect(rejected.visible).to_equal(true)
expect(rejected.border_color).to_equal("subtle")
expect(rejected.footer).to_equal("Teammate is continuing to work. You may request shutdown again later.")
expect(getShutdownMessageSummary("shutdown-rejected:Grace|Still running")).to_equal("[Shutdown Rejected] Grace: Still running")
```

</details>

#### should summarize team memory counts

- Format saved memory and collapsed read/search/write parts
   - Expected: teamMemSavedPart(0).present is false
   - Expected: saved.present is true
   - Expected: saved.segment equals `2 team memories`
   - Expected: checkHasTeamMemOps(counts) is true
   - Expected: teamMemCollapsedParts(counts, true, false) equals `Recalling 1 team memory, searching team memories, writing 2 team memories`
   - Expected: teamMemCollapsedParts(TeamMemCounts.new(0, 0, 1), false, true) equals `wrote 1 team memory`
   - Expected: checkHasTeamMemOps(TeamMemCounts.new(0, 0, 0)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Format saved memory and collapsed read/search/write parts")
expect(teamMemSavedPart(0).present).to_equal(false)
val saved = teamMemSavedPart(2)
expect(saved.present).to_equal(true)
expect(saved.segment).to_equal("2 team memories")
val counts = TeamMemCounts.new(1, 1, 2)
expect(checkHasTeamMemOps(counts)).to_equal(true)
expect(teamMemCollapsedParts(counts, true, false)).to_equal("Recalling 1 team memory, searching team memories, writing 2 team memories")
expect(teamMemCollapsedParts(TeamMemCounts.new(0, 0, 1), false, true)).to_equal("wrote 1 team memory")
expect(checkHasTeamMemOps(TeamMemCounts.new(0, 0, 0))).to_equal(false)
```

</details>

#### should render user bash and agent notification tags

- Extract tagged bash input and agent status summaries
   - Expected: bash.visible is true
   - Expected: bash.input equals `make test`
   - Expected: bash.prefix equals `! `
   - Expected: bash.margin_top equals `1`
   - Expected: userBashInputMessage("plain", false).visible is false
   - Expected: note.visible is true
   - Expected: note.summary equals `Done`
   - Expected: note.color equals `success`
   - Expected: note.margin_top equals `1`
   - Expected: userAgentNotificationLine(note) equals `"● Done")`
   - Expected: userAgentNotificationStatusColor("failed") equals `error`
   - Expected: userAgentNotificationStatusColor("killed") equals `warning`
   - Expected: userAgentNotificationMessage("plain", false).visible is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Extract tagged bash input and agent status summaries")
val bash = userBashInputMessage("<bash-input>make test</bash-input>", true)
expect(bash.visible).to_equal(true)
expect(bash.input).to_equal("make test")
expect(bash.prefix).to_equal("! ")
expect(bash.margin_top).to_equal(1)
expect(userBashInputMessage("plain", false).visible).to_equal(false)
val note = userAgentNotificationMessage("<summary>Done</summary><status>completed</status>", true)
expect(note.visible).to_equal(true)
expect(note.summary).to_equal("Done")
expect(note.color).to_equal("success")
expect(note.margin_top).to_equal(1)
expect(userAgentNotificationLine(note)).to_equal("● Done")
expect(userAgentNotificationStatusColor("failed")).to_equal("error")
expect(userAgentNotificationStatusColor("killed")).to_equal("warning")
expect(userAgentNotificationMessage("plain", false).visible).to_equal(false)
```

</details>

#### should render user bash output, command, and image messages

- Extract bash output tags, slash command tags, and image link metadata
   - Expected: output.stdout equals `/tmp/out\npreview`
   - Expected: output.stderr equals `err`
   - Expected: output.verbose is true
   - Expected: userBashOutputSummary(output) equals `stdout:/tmp/out\npreview|stderr:err`
   - Expected: command.visible is true
   - Expected: command.content equals `/commit --amend`
   - Expected: command.margin_top equals `1`
   - Expected: skill.content equals `Skill(review)`
   - Expected: skill.skill_format is true
   - Expected: userCommandMessage("plain", false).visible is false
   - Expected: image.label equals `[Image #7]`
   - Expected: image.clickable is true
   - Expected: image.link_url equals `file:///tmp/img.png`
   - Expected: image.wrapped_in_message_response is true
   - Expected: userImageMessage(0, "", false, true).label equals `[Image]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Extract bash output tags, slash command tags, and image link metadata")
val output = userBashOutputMessage("<bash-stdout><persisted-output>/tmp/out\npreview</persisted-output></bash-stdout><bash-stderr>err</bash-stderr>", true)
expect(output.stdout).to_equal("/tmp/out\npreview")
expect(output.stderr).to_equal("err")
expect(output.verbose).to_equal(true)
expect(userBashOutputSummary(output)).to_equal("stdout:/tmp/out\npreview|stderr:err")
val command = userCommandMessage("<command-message>commit</command-message><command-args>--amend</command-args>", true)
expect(command.visible).to_equal(true)
expect(command.content).to_equal("/commit --amend")
expect(command.margin_top).to_equal(1)
val skill = userCommandMessage("<command-message>review</command-message><skill-format>true</skill-format>", false)
expect(skill.content).to_equal("Skill(review)")
expect(skill.skill_format).to_equal(true)
expect(userCommandMessage("plain", false).visible).to_equal(false)
val image = userImageMessage(7, "/tmp/img.png", true, false)
expect(image.label).to_equal("[Image #7]")
expect(image.clickable).to_equal(true)
expect(image.link_url).to_equal("file:///tmp/img.png")
expect(image.wrapped_in_message_response).to_equal(true)
expect(userImageMessage(0, "", false, true).label).to_equal("[Image]")
```

</details>

#### should render user plan messages

- Render plan content with plan-mode border
   - Expected: plan.header equals `Plan to implement`
   - Expected: plan.plan_content equals `1. Build\n2. Test`
   - Expected: plan.border_color equals `planMode`
   - Expected: plan.margin_top equals `1`
   - Expected: userPlanMessage("No margin", false).margin_top equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render plan content with plan-mode border")
val plan = userPlanMessage("1. Build\n2. Test", true)
expect(plan.header).to_equal("Plan to implement")
expect(plan.plan_content).to_equal("1. Build\n2. Test")
expect(plan.border_color).to_equal("planMode")
expect(plan.margin_top).to_equal(1)
expect(userPlanMessage("No margin", false).margin_top).to_equal(0)
```

</details>

#### should render plan approval messages

- Parse plan approval requests and responses
   - Expected: request.visible is true
   - Expected: request.title equals `Plan Approval Request from Ada`
   - Expected: request.body equals `Do it`
   - Expected: request.footer equals `Plan file: /tmp/plan.md`
   - Expected: approved.title equals `"✓ Plan Approved by Ada")`
   - Expected: rejected.body equals `Feedback: Too broad`
   - Expected: getPlanApprovalSummary("{\"type\":\"plan_approval_response\",\"approved\":false,\"feedback\":\"Too broad\"}") equals `[Plan Rejected] Too broad`
   - Expected: formatTeammateMessageContent("{\"type\":\"idle_notification\",\"completedTaskId\":\"42\",\"completedStatus\":\"done\",\"summary\":\"Waiting\"}") equals `"Agent idle · Task 42 done · Last DM: Waiting")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse plan approval requests and responses")
val request = tryRenderPlanApprovalMessage("{\"type\":\"plan_approval_request\",\"from\":\"Ada\",\"planFilePath\":\"/tmp/plan.md\",\"planContent\":\"Do it\"}", "Claude")
expect(request.visible).to_equal(true)
expect(request.title).to_equal("Plan Approval Request from Ada")
expect(request.body).to_equal("Do it")
expect(request.footer).to_equal("Plan file: /tmp/plan.md")
val approved = tryRenderPlanApprovalMessage("{\"type\":\"plan_approval_response\",\"approved\":true}", "Ada")
expect(approved.title).to_equal("✓ Plan Approved by Ada")
val rejected = tryRenderPlanApprovalMessage("{\"type\":\"plan_approval_response\",\"approved\":false,\"feedback\":\"Too broad\"}", "Ada")
expect(rejected.body).to_equal("Feedback: Too broad")
expect(getPlanApprovalSummary("{\"type\":\"plan_approval_response\",\"approved\":false,\"feedback\":\"Too broad\"}")).to_equal("[Plan Rejected] Too broad")
expect(formatTeammateMessageContent("{\"type\":\"idle_notification\",\"completedTaskId\":\"42\",\"completedStatus\":\"done\",\"summary\":\"Waiting\"}")).to_equal("Agent idle · Task 42 done · Last DM: Waiting")
```

</details>

#### should render rejected tool-use messages

- Match the fixed dim response shown for rejected tool use
   - Expected: rejected.text equals `Tool use rejected`
   - Expected: rejected.dim is true
   - Expected: rejected.response_height equals `1`
   - Expected: rejectedPlan.title equals `User rejected Claude's plan:`
   - Expected: rejectedPlan.plan equals `1. Build\n2. Test`
   - Expected: rejectedPlan.border_color equals `planMode`
   - Expected: rejectedPlan.overflow equals `hidden`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Match the fixed dim response shown for rejected tool use")
val rejected = rejectedToolUseMessage()
expect(rejected.text).to_equal("Tool use rejected")
expect(rejected.dim).to_equal(true)
expect(rejected.response_height).to_equal(1)
val rejectedPlan = rejectedPlanMessage("1. Build\n2. Test")
expect(rejectedPlan.title).to_equal("User rejected Claude's plan:")
expect(rejectedPlan.plan).to_equal("1. Build\n2. Test")
expect(rejectedPlan.border_color).to_equal("planMode")
expect(rejectedPlan.overflow).to_equal("hidden")
```

</details>

#### should render channel, memory, local command, and prompt user messages

- Cover worker-added message helpers
   - Expected: channel.visible is true
   - Expected: channel.display_source equals `linear`
   - Expected: channel.user equals `Ada`
   - Expected: channel.body equals `hello team`
   - Expected: channel.margin_top equals `1`
   - Expected: userChannelMessageLine(channel) equals `"← linear · Ada: hello team")`
   - Expected: memory.visible is true
   - Expected: memory.marker equals `#`
   - Expected: memory.saving_text equals `Got it.`
   - Expected: userMemoryInputMessage("plain", false).visible is false
   - Expected: localOutput.visible is true
   - Expected: localOutput.lines.len() equals `1`
   - Expected: localOutput.lines[0].mode equals `cloud-launch`
   - Expected: localOutput.lines[0].label equals `Run checks`
   - Expected: stderrOnly.lines[0].key equals `stderr`
   - Expected: userLocalCommandOutputMessage("").empty_message equals `(no content)`
   - Expected: prompt.visible is true
   - Expected: prompt.use_brief_layout is true
   - Expected: prompt.timestamp equals `10:00`
   - Expected: userPromptMessage("", false, false, "", false, false, false, false, false, false, "", false).logged_error equals `No content found in user prompt message`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Cover worker-added message helpers")
val channel = userChannelMessage("<channel source=\"mcp:linear\" user=\"Ada\">  hello\nteam  </channel>", true)
expect(channel.visible).to_equal(true)
expect(channel.display_source).to_equal("linear")
expect(channel.user).to_equal("Ada")
expect(channel.body).to_equal("hello team")
expect(channel.margin_top).to_equal(1)
expect(userChannelMessageLine(channel)).to_equal("← linear · Ada: hello team")
val memory = userMemoryInputMessage("<user-memory-input>Save this</user-memory-input>", true)
expect(memory.visible).to_equal(true)
expect(memory.marker).to_equal("#")
expect(memory.saving_text).to_equal("Got it.")
expect(userMemoryInputMessage("plain", false).visible).to_equal(false)
val localOutput = userLocalCommandOutputMessage("<local-command-stdout>◇ Run checks · done\nall good</local-command-stdout>")
expect(localOutput.visible).to_equal(true)
expect(localOutput.lines.len()).to_equal(1)
expect(localOutput.lines[0].mode).to_equal("cloud-launch")
expect(localOutput.lines[0].label).to_equal("Run checks")
val stderrOnly = userLocalCommandOutputMessage("<local-command-stderr>err</local-command-stderr>")
expect(stderrOnly.lines[0].key).to_equal("stderr")
expect(userLocalCommandOutputMessage("").empty_message).to_equal("(no content)")
val prompt = userPromptMessage("hello", true, false, "10:00", true, true, false, false, false, true, "", false)
expect(prompt.visible).to_equal(true)
expect(prompt.use_brief_layout).to_equal(true)
expect(prompt.timestamp).to_equal("10:00")
expect(userPromptMessage("", false, false, "", false, false, false, false, false, false, "", false).logged_error).to_equal("No content found in user prompt message")
```

</details>

#### should render system API error retry messages

- Hide early retries, truncate non-verbose errors, and include timeout hint
   - Expected: systemAPIErrorMessage(3, "hidden", 1000, 5, false, 0, "").visible is false
   - Expected: render.visible is true
   - Expected: render.displayed_error equals `abcdef`
   - Expected: render.retry_in_seconds equals `3`
   - Expected: render.retry_unit equals `seconds`
   - Expected: render.retry_line equals `"Retrying in 3 seconds... (attempt 4/5) · API_TIMEOUT_MS=30000ms, try increas... (full value in folded executable source)`
   - Expected: systemAPIErrorNextCountdownMs(1000) equals `2000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Hide early retries, truncate non-verbose errors, and include timeout hint")
expect(systemAPIErrorMessage(3, "hidden", 1000, 5, false, 0, "").visible).to_equal(false)
val render = systemAPIErrorMessage(4, "abcdef", 2500, 5, false, 0, "30000")
expect(render.visible).to_equal(true)
expect(render.displayed_error).to_equal("abcdef")
expect(render.retry_in_seconds).to_equal(3)
expect(render.retry_unit).to_equal("seconds")
expect(render.retry_line).to_equal("Retrying in 3 seconds... (attempt 4/5) · API_TIMEOUT_MS=30000ms, try increasing it")
expect(systemAPIErrorNextCountdownMs(1000)).to_equal(2000)
```

</details>

#### should render system text messages

- Cover duration, memory, stop-hook, bridge, and filtered info states
- var duration = SystemTextMessageInput new
   - Expected: systemTextMessage(duration).text equals `"Worked for 1m 5s · 25 / 100 (25%) · 1 nudge")`
- var memory = SystemTextMessageInput new
   - Expected: systemTextMessage(memory).text equals `"Saved 1 memory · 1 team memory")`
- var hook = SystemTextMessageInput new
- hook hook infos = [SystemHookInfo new
   - Expected: systemTextMessage(hook).text equals `Ran 1 stop hook (700ms)`
- var bridge = SystemTextMessageInput new
   - Expected: systemTextMessage(bridge).child_lines[1] equals `https://claude.example`
   - Expected: systemTextMessage(SystemTextMessageInput.new("plain", "info", "skip")).visible is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Cover duration, memory, stop-hook, bridge, and filtered info states")
var duration = SystemTextMessageInput.new("turn_duration", "info", "")
duration.duration_ms = 65000
duration.budget_limit = 100
duration.budget_tokens = 25
duration.budget_nudges = 1
expect(systemTextMessage(duration).text).to_equal("Worked for 1m 5s · 25 / 100 (25%) · 1 nudge")
var memory = SystemTextMessageInput.new("memory_saved", "info", "")
memory.written_paths = ["/a", "/b"]
memory.team_saved_count = 1
memory.team_saved_segment = "1 team memory"
expect(systemTextMessage(memory).text).to_equal("Saved 1 memory · 1 team memory")
var hook = SystemTextMessageInput.new("stop_hook_summary", "info", "")
hook.hook_count = 1
hook.hook_infos = [SystemHookInfo.new("prompt", "review", 700)]
expect(systemTextMessage(hook).text).to_equal("Ran 1 stop hook (700ms)")
var bridge = SystemTextMessageInput.new("bridge_status", "info", "")
bridge.url = "https://claude.example"
expect(systemTextMessage(bridge).child_lines[1]).to_equal("https://claude.example")
expect(systemTextMessage(SystemTextMessageInput.new("plain", "info", "skip")).visible).to_equal(false)
```

</details>

#### should describe debug utility output

- Flatten, truncate, redact, and capture bridge skip metadata
   - Expected: debugFlatten("a\nb") equals `a\\nb`
   - Expected: redactSecretValue("short") equals `[REDACTED]`
   - Expected: redactSecretValue("1234567890abcdef") equals `12345678...cdef`
   - Expected: describeAxiosError(err) equals `request failed: too many`
   - Expected: extractHttpStatus(err) equals `429`
   - Expected: extractErrorDetail("", "fallback") equals `fallback`
   - Expected: event.reason equals `capacity`
   - Expected: event.debug_message equals `sleeping`
   - Expected: event.v2 is true
   - Expected: debugTruncate("small") equals `small`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Flatten, truncate, redact, and capture bridge skip metadata")
expect(debugFlatten("a\nb")).to_equal("a\\nb")
expect(redactSecretValue("short")).to_equal("[REDACTED]")
expect(redactSecretValue("1234567890abcdef")).to_equal("12345678...cdef")
val err = DebugHttpError.new("request failed", 429, "too many")
expect(describeAxiosError(err)).to_equal("request failed: too many")
expect(extractHttpStatus(err)).to_equal(429)
expect(extractErrorDetail("", "fallback")).to_equal("fallback")
val event = logBridgeSkip("capacity", "sleeping", true, true)
expect(event.reason).to_equal("capacity")
expect(event.debug_message).to_equal("sleeping")
expect(event.v2).to_equal(true)
expect(debugTruncate("small")).to_equal("small")
```

</details>

#### should pin source-modeled line counts

- Expose modeled source sizes for parity checker
   - Expected: bridgeEnabledSourceLinesModeled() equals `202`
   - Expected: bridgeStatusUtilSourceLinesModeled() equals `163`
   - Expected: capacityWakeSourceLinesModeled() equals `56`
   - Expected: codeSessionApiSourceLinesModeled() equals `168`
   - Expected: debugUtilsSourceLinesModeled() equals `141`
   - Expected: envLessBridgeConfigSourceLinesModeled() equals `165`
   - Expected: highlightedThinkingTextSourceLinesModeled() equals `161`
   - Expected: hookProgressMessageSourceLinesModeled() equals `115`
   - Expected: inboundAttachmentsSourceLinesModeled() equals `175`
   - Expected: inboundMessagesSourceLinesModeled() equals `80`
   - Expected: nullRenderingAttachmentsSourceLinesModeled() equals `70`
   - Expected: pollConfigDefaultsSourceLinesModeled() equals `82`
   - Expected: planApprovalMessageSourceLinesModeled() equals `221`
   - Expected: rateLimitMessageSourceLinesModeled() equals `170`
   - Expected: shutdownMessageSourceLinesModeled() equals `131`
   - Expected: systemAPIErrorMessageSourceLinesModeled() equals `140`
   - Expected: systemTextMessageSourceLinesModeled() equals `826`
   - Expected: taskAssignmentMessageSourceLinesModeled() equals `75`
   - Expected: teamMemCollapsedSourceLinesModeled() equals `139`
   - Expected: teamMemSavedSourceLinesModeled() equals `19`
   - Expected: userAgentNotificationMessageSourceLinesModeled() equals `82`
   - Expected: userBashInputMessageSourceLinesModeled() equals `57`
   - Expected: userBashOutputMessageSourceLinesModeled() equals `53`
   - Expected: userChannelMessageSourceLinesModeled() equals `136`
   - Expected: userCommandMessageSourceLinesModeled() equals `107`
   - Expected: userImageMessageSourceLinesModeled() equals `58`
   - Expected: userLocalCommandOutputMessageSourceLinesModeled() equals `166`
   - Expected: userMemoryInputMessageSourceLinesModeled() equals `74`
   - Expected: userPlanMessageSourceLinesModeled() equals `41`
   - Expected: userPromptMessageSourceLinesModeled() equals `79`
   - Expected: rejectedPlanMessageSourceLinesModeled() equals `30`
   - Expected: rejectedToolUseMessageSourceLinesModeled() equals `15`
   - Expected: groupedToolUseContentSourceLinesModeled() equals `57`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expose modeled source sizes for parity checker")
expect(bridgeEnabledSourceLinesModeled()).to_equal(202)
expect(bridgeStatusUtilSourceLinesModeled()).to_equal(163)
expect(capacityWakeSourceLinesModeled()).to_equal(56)
expect(codeSessionApiSourceLinesModeled()).to_equal(168)
expect(debugUtilsSourceLinesModeled()).to_equal(141)
expect(envLessBridgeConfigSourceLinesModeled()).to_equal(165)
expect(highlightedThinkingTextSourceLinesModeled()).to_equal(161)
expect(hookProgressMessageSourceLinesModeled()).to_equal(115)
expect(inboundAttachmentsSourceLinesModeled()).to_equal(175)
expect(inboundMessagesSourceLinesModeled()).to_equal(80)
expect(nullRenderingAttachmentsSourceLinesModeled()).to_equal(70)
expect(pollConfigDefaultsSourceLinesModeled()).to_equal(82)
expect(planApprovalMessageSourceLinesModeled()).to_equal(221)
expect(rateLimitMessageSourceLinesModeled()).to_equal(170)
expect(shutdownMessageSourceLinesModeled()).to_equal(131)
expect(systemAPIErrorMessageSourceLinesModeled()).to_equal(140)
expect(systemTextMessageSourceLinesModeled()).to_equal(826)
expect(taskAssignmentMessageSourceLinesModeled()).to_equal(75)
expect(teamMemCollapsedSourceLinesModeled()).to_equal(139)
expect(teamMemSavedSourceLinesModeled()).to_equal(19)
expect(userAgentNotificationMessageSourceLinesModeled()).to_equal(82)
expect(userBashInputMessageSourceLinesModeled()).to_equal(57)
expect(userBashOutputMessageSourceLinesModeled()).to_equal(53)
expect(userChannelMessageSourceLinesModeled()).to_equal(136)
expect(userCommandMessageSourceLinesModeled()).to_equal(107)
expect(userImageMessageSourceLinesModeled()).to_equal(58)
expect(userLocalCommandOutputMessageSourceLinesModeled()).to_equal(166)
expect(userMemoryInputMessageSourceLinesModeled()).to_equal(74)
expect(userPlanMessageSourceLinesModeled()).to_equal(41)
expect(userPromptMessageSourceLinesModeled()).to_equal(79)
expect(rejectedPlanMessageSourceLinesModeled()).to_equal(30)
expect(rejectedToolUseMessageSourceLinesModeled()).to_equal(15)
expect(groupedToolUseContentSourceLinesModeled()).to_equal(57)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [N/A - strict llm_caret Claude CLI parity lane.](N/A - strict llm_caret Claude CLI parity lane.)
- **Plan:** [N/A - target selected from strict checker output.](N/A - target selected from strict checker output.)
- **Design:** [N/A - source mirror for Claude CLI bridge and message helpers.](N/A - source mirror for Claude CLI bridge and message helpers.)
- **Research:** [N/A - upstream TypeScript files are the source reference.](N/A - upstream TypeScript files are the source reference.)


</details>
