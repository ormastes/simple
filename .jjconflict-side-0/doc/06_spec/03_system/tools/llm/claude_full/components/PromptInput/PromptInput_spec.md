# Claude Full PromptInput Slice

> Focused coverage for top-level PromptInput shell render and first-pass

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full PromptInput Slice

Focused coverage for top-level PromptInput shell render and first-pass

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/PromptInput/PromptInput_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused coverage for top-level PromptInput shell render and first-pass
interaction route behavior from components/PromptInput/PromptInput.tsx.

## Scenarios

### Claude full PromptInput parity

#### should model top level prompt shell routes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model top level prompt shell routes
- Check shell rendering
   - Expected: promptInputFrameRoute(true, false) equals `external editor message`
   - Expected: promptInputFrameRoute(false, false) equals `bordered prompt shell`
   - Expected: promptInputFrameRoute(false, true) equals `swarm banner prompt shell`
   - Expected: queuedCommandsRoute(false, true) equals `queued commands visible`
   - Expected: queuedCommandsRoute(true, true) equals `queued commands hidden`
   - Expected: stashNoticeRoute(true) equals `stash notice visible`
   - Expected: stashNoticeRoute(false) equals `stash notice hidden`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model top level prompt shell routes")
step("Check shell rendering")
expect(promptInputFrameRoute(true, false)).to_equal("external editor message")
expect(promptInputFrameRoute(false, false)).to_equal("bordered prompt shell")
expect(promptInputFrameRoute(false, true)).to_equal("swarm banner prompt shell")
expect(queuedCommandsRoute(false, true)).to_equal("queued commands visible")
expect(queuedCommandsRoute(true, true)).to_equal("queued commands hidden")
expect(stashNoticeRoute(true)).to_equal("stash notice visible")
expect(stashNoticeRoute(false)).to_equal("stash notice hidden")
```

</details>

#### should model input footer and fullscreen routes

- should model input footer and fullscreen routes
- Check prompt internals
   - Expected: modeIndicatorOrderRoute(false) equals `mode indicator before input`
   - Expected: modeIndicatorOrderRoute(true) equals `mode indicator before swarm input`
   - Expected: inputKindRoute(true) equals `vim input`
   - Expected: inputKindRoute(false) equals `plain text input`
   - Expected: borderTextRoute(true, true) equals `fast border with hint`
   - Expected: borderTextRoute(true, false) equals `fast border`
   - Expected: footerRoute(false) equals `footer`
   - Expected: footerRoute(true) equals `footer with tasks dialog`
   - Expected: fullscreenNotificationsRoute(false, false, false) equals `notifications hidden`
   - Expected: fullscreenNotificationsRoute(true, true, false) equals `notifications height zero`
   - Expected: fullscreenNotificationsRoute(true, false, false) equals `notifications overlay`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model input footer and fullscreen routes")
step("Check prompt internals")
expect(modeIndicatorOrderRoute(false)).to_equal("mode indicator before input")
expect(modeIndicatorOrderRoute(true)).to_equal("mode indicator before swarm input")
expect(inputKindRoute(true)).to_equal("vim input")
expect(inputKindRoute(false)).to_equal("plain text input")
expect(borderTextRoute(true, true)).to_equal("fast border with hint")
expect(borderTextRoute(true, false)).to_equal("fast border")
expect(footerRoute(false)).to_equal("footer")
expect(footerRoute(true)).to_equal("footer with tasks dialog")
expect(fullscreenNotificationsRoute(false, false, false)).to_equal("notifications hidden")
expect(fullscreenNotificationsRoute(true, true, false)).to_equal("notifications height zero")
expect(fullscreenNotificationsRoute(true, false, false)).to_equal("notifications overlay")
```

</details>

#### should model first pass input interactions

- should model first pass input interactions
- Check interactions
   - Expected: typingRoute() equals `clear footer selection and abort suggestions`
   - Expected: historyNavigationRoute("up", true) equals `up history`
   - Expected: historyNavigationRoute("down", false) equals `stay in multiline input`
   - Expected: submitRoute(true) equals `submit blocked`
   - Expected: submitRoute(false) equals `submit prompt`
   - Expected: insertTextRoute("hello", "world", 5, true) equals `hello world`
   - Expected: insertTextRoute("hello ", "world", 6, false) equals `hello world`
   - Expected: promptInputSourceLinesModeled() equals `2338`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model first pass input interactions")
step("Check interactions")
expect(typingRoute()).to_equal("clear footer selection and abort suggestions")
expect(historyNavigationRoute("up", true)).to_equal("up history")
expect(historyNavigationRoute("down", false)).to_equal("stay in multiline input")
expect(submitRoute(true)).to_equal("submit blocked")
expect(submitRoute(false)).to_equal("submit prompt")
expect(insertTextRoute("hello", "world", 5, true)).to_equal("hello world")
expect(insertTextRoute("hello ", "world", 6, false)).to_equal("hello world")
expect(promptInputSourceLinesModeled()).to_equal(2338)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `7941b8c6b48de73169794649ba1adf603bf5b894b0e7845d6a141c147478bdde`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7941b8c6b48de73169794649ba1adf603bf5b894b0e7845d6a141c147478bdde`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7941b8c6b48de73169794649ba1adf603bf5b894b0e7845d6a141c147478bdde`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/components/PromptInput/PromptInput_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/PromptInput/PromptInput_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/PromptInput/PromptInput_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/PromptInput/PromptInput_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/PromptInput/PromptInput_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/PromptInput/PromptInput_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model top level prompt shell routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/PromptInput/PromptInput_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model top level prompt shell routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/PromptInput/PromptInput_spec.spl:31:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model input footer and fullscreen routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/PromptInput/PromptInput_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model input footer and fullscreen routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/PromptInput/PromptInput_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model first pass input interactions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/PromptInput/PromptInput_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model first pass input interactions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
