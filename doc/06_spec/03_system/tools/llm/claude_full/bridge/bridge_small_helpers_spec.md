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
| 6 | 6 | 0 | 0 |

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
normalization, bridge polling defaults, grouped tool-use rendering state, debug
message formatting, and source line parity helpers.

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
   - Expected: capacityWakeSourceLinesModeled() equals `56`
   - Expected: debugUtilsSourceLinesModeled() equals `141`
   - Expected: inboundMessagesSourceLinesModeled() equals `80`
   - Expected: pollConfigDefaultsSourceLinesModeled() equals `82`
   - Expected: groupedToolUseContentSourceLinesModeled() equals `57`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expose modeled source sizes for parity checker")
expect(capacityWakeSourceLinesModeled()).to_equal(56)
expect(debugUtilsSourceLinesModeled()).to_equal(141)
expect(inboundMessagesSourceLinesModeled()).to_equal(80)
expect(pollConfigDefaultsSourceLinesModeled()).to_equal(82)
expect(groupedToolUseContentSourceLinesModeled()).to_equal(57)
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


## Related Documentation

- **Requirements:** [N/A - strict llm_caret Claude CLI parity lane.](N/A - strict llm_caret Claude CLI parity lane.)
- **Plan:** [N/A - target selected from strict checker output.](N/A - target selected from strict checker output.)
- **Design:** [N/A - source mirror for Claude CLI bridge and message helpers.](N/A - source mirror for Claude CLI bridge and message helpers.)
- **Research:** [N/A - upstream TypeScript files are the source reference.](N/A - upstream TypeScript files are the source reference.)


</details>
