# Claude Full Screens REPL Slice

> Focused coverage for REPL transcript/search/footer, query lifecycle, command

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Screens REPL Slice

Focused coverage for REPL transcript/search/footer, query lifecycle, command

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/screens/REPL_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused coverage for REPL transcript/search/footer, query lifecycle, command
execution, permissions, queue handling, suspend/resume/exit, and stdout routes.

## Scenarios

### Claude full screens REPL parity

#### should model transcript search footer and title routes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model transcript search footer and title routes
- Check visible transcript/search behavior
   - Expected: props.transcriptMode is true
   - Expected: screen.active is true
   - Expected: proactiveNoOpSubscribeRoute() equals `proactive no op unsubscribe`
   - Expected: proactiveFalseRoute() is false
   - Expected: suggestBgPrNoopRoute() equals `suggest background pr noop`
   - Expected: shouldShowAntModelSwitchRoute("ant", true, false) is true
   - Expected: shouldShowAntModelSwitchRoute("ant", true, true) is false
   - Expected: medianRoute(0, true) equals `median none`
   - Expected: medianRoute(3, true) equals `median middle`
   - Expected: transcriptModeFooterRoute(true, 3, 1) equals `footer search matches`
   - Expected: transcriptSearchBarRoute("err", true, 2) equals `search focused with matches`
   - Expected: animatedTerminalTitleRoute(false, "build", false) equals `animated renamed terminal title`
   - Expected: replRoute("main", false, true) equals `render transcript screen`
   - Expected: transcriptRenderRoute("transcript", false, true) equals `alternate screen transcript keybindings search`
   - Expected: transcriptRenderRoute("transcript", true, true) equals `render transcript dump`
   - Expected: transcriptKeyRoute("/", 0, 1) equals `activate transcript search arm anchor`
   - Expected: transcriptKeyRoute("n", 4, 3) equals `advance transcript search jump 3`
   - Expected: transcriptKeyRoute("v", 0, 1) equals `export transcript open editor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model transcript search footer and title routes")
step("Check visible transcript/search behavior")
val props = Props.new(true, false, "hello")
expect(props.transcriptMode).to_equal(true)
val screen = Screen.new("repl", true)
expect(screen.active).to_equal(true)
expect(proactiveNoOpSubscribeRoute()).to_equal("proactive no op unsubscribe")
expect(proactiveFalseRoute()).to_equal(false)
expect(suggestBgPrNoopRoute()).to_equal("suggest background pr noop")
expect(shouldShowAntModelSwitchRoute("ant", true, false)).to_equal(true)
expect(shouldShowAntModelSwitchRoute("ant", true, true)).to_equal(false)
expect(medianRoute(0, true)).to_equal("median none")
expect(medianRoute(3, true)).to_equal("median middle")
expect(transcriptModeFooterRoute(true, 3, 1)).to_equal("footer search matches")
expect(transcriptSearchBarRoute("err", true, 2)).to_equal("search focused with matches")
expect(animatedTerminalTitleRoute(false, "build", false)).to_equal("animated renamed terminal title")
expect(replRoute("main", false, true)).to_equal("render transcript screen")
expect(transcriptRenderRoute("transcript", false, true)).to_equal("alternate screen transcript keybindings search")
expect(transcriptRenderRoute("transcript", true, true)).to_equal("render transcript dump")
expect(transcriptKeyRoute("/", 0, 1)).to_equal("activate transcript search arm anchor")
expect(transcriptKeyRoute("n", 4, 3)).to_equal("advance transcript search jump 3")
expect(transcriptKeyRoute("v", 0, 1)).to_equal("export transcript open editor")
```

</details>

#### should model query command permission and queue routes

- should model query command permission and queue routes
- Check hidden query and command lifecycle
   - Expected: remoteCalloutRoute(true, true) equals `show remote mcp callout`
   - Expected: setMessagesRoute(true, false) equals `restore message sync`
   - Expected: setMessagesRoute(false, true) equals `insert unseen divider`
   - Expected: scrollRoute(true, true) equals `preserve user scroll`
   - Expected: scrollRoute(false, true) equals `repin scroll to bottom`
   - Expected: queryEventRoute("assistant", true, false) equals `append streaming assistant text`
   - Expected: queryEventRoute("tool", false, true) equals `update in progress tool use`
   - Expected: onQueryRoute(true, false, true) equals `submit first query with notification attachments`
   - Expected: onQueryRoute(false, true, false) equals `start background query`
   - Expected: submitRoute(true, true, true, false, false) equals `execute immediate local command while loading`
   - Expected: submitRoute(false, false, false, true, false) equals `remote create user message send`
   - Expected: submitRoute(false, false, false, false, true) equals `handle prompt submit with pasted refs`
   - Expected: queryGuardRoute(false, false, false, false) equals `enqueue input because query guard busy`
   - Expected: queryGuardRoute(true, true, false, false) equals `query guard end reset loading notify bridge`
   - Expected: queryGuardRoute(true, false, true, false) equals `restore interrupted message into prompt`
   - Expected: executeImmediateCommandRoute(true, true, 0) equals `queue command for dialog`
   - Expected: executeImmediateCommandRoute(true, false, 5) equals `execute command with pasted text refs`
   - Expected: focusedInputDialogRoute(true, false, false) equals `permission dialog focused`
   - Expected: focusedInputDialogPriorityRoute(true, true, true, true, false) equals `tool permission dialog focused`
   - Expected: focusedInputDialogPriorityRoute(false, true, true, true, false) equals `worker request dialog focused`
   - Expected: focusedInputDialogPriorityRoute(false, false, false, false, true) equals `prompt input suppressed by active dialog`
   - Expected: handleQueuedCommandOnCancelRoute(true, true) equals `restore queued command input`
   - Expected: toolPermissionOverlayRoute(true, false, false) equals `show permission overlay`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model query command permission and queue routes")
step("Check hidden query and command lifecycle")
expect(remoteCalloutRoute(true, true)).to_equal("show remote mcp callout")
expect(setMessagesRoute(true, false)).to_equal("restore message sync")
expect(setMessagesRoute(false, true)).to_equal("insert unseen divider")
expect(scrollRoute(true, true)).to_equal("preserve user scroll")
expect(scrollRoute(false, true)).to_equal("repin scroll to bottom")
expect(queryEventRoute("assistant", true, false)).to_equal("append streaming assistant text")
expect(queryEventRoute("tool", false, true)).to_equal("update in progress tool use")
expect(onQueryRoute(true, false, true)).to_equal("submit first query with notification attachments")
expect(onQueryRoute(false, true, false)).to_equal("start background query")
expect(submitRoute(true, true, true, false, false)).to_equal("execute immediate local command while loading")
expect(submitRoute(false, false, false, true, false)).to_equal("remote create user message send")
expect(submitRoute(false, false, false, false, true)).to_equal("handle prompt submit with pasted refs")
expect(queryGuardRoute(false, false, false, false)).to_equal("enqueue input because query guard busy")
expect(queryGuardRoute(true, true, false, false)).to_equal("query guard end reset loading notify bridge")
expect(queryGuardRoute(true, false, true, false)).to_equal("restore interrupted message into prompt")
expect(executeImmediateCommandRoute(true, true, 0)).to_equal("queue command for dialog")
expect(executeImmediateCommandRoute(true, false, 5)).to_equal("execute command with pasted text refs")
expect(focusedInputDialogRoute(true, false, false)).to_equal("permission dialog focused")
expect(focusedInputDialogPriorityRoute(true, true, true, true, false)).to_equal("tool permission dialog focused")
expect(focusedInputDialogPriorityRoute(false, true, true, true, false)).to_equal("worker request dialog focused")
expect(focusedInputDialogPriorityRoute(false, false, false, false, true)).to_equal("prompt input suppressed by active dialog")
expect(handleQueuedCommandOnCancelRoute(true, true)).to_equal("restore queued command input")
expect(toolPermissionOverlayRoute(true, false, false)).to_equal("show permission overlay")
```

</details>

#### should model exit transcript suspend and stdout routes

- should model exit transcript suspend and stdout routes
- Check exit and lifecycle routes
   - Expected: handleExitRoute(true, false, false) equals `confirm exit running agents`
   - Expected: handleExitRoute(false, true, false) equals `confirm exit running tools`
   - Expected: handleExitRoute(false, false, true) equals `force exit`
   - Expected: transcriptRoute("enter") equals `enter transcript mode`
   - Expected: transcriptRoute("search") equals `update transcript search matches`
   - Expected: cancelRoute("toolPermission", false, false) equals `abort head tool permission and clear queue`
   - Expected: cancelRoute("prompt", false, false) equals `normal abort restore interrupted prompt`
   - Expected: cancelRoute("prompt", true, false) equals `cancel queued input`
   - Expected: suspendResumeRoute("suspend") equals `suspend repl input`
   - Expected: suspendResumeRoute("resume") equals `resume repl input`
   - Expected: appendStdoutRoute(false, "out") equals `buffer stdout until idle`
   - Expected: appendStdoutRoute(true, "out") equals `append stdout when idle`
   - Expected: appendStdoutRoute(true, "") equals `skip empty stdout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model exit transcript suspend and stdout routes")
step("Check exit and lifecycle routes")
expect(handleExitRoute(true, false, false)).to_equal("confirm exit running agents")
expect(handleExitRoute(false, true, false)).to_equal("confirm exit running tools")
expect(handleExitRoute(false, false, true)).to_equal("force exit")
expect(transcriptRoute("enter")).to_equal("enter transcript mode")
expect(transcriptRoute("search")).to_equal("update transcript search matches")
expect(cancelRoute("toolPermission", false, false)).to_equal("abort head tool permission and clear queue")
expect(cancelRoute("prompt", false, false)).to_equal("normal abort restore interrupted prompt")
expect(cancelRoute("prompt", true, false)).to_equal("cancel queued input")
expect(suspendResumeRoute("suspend")).to_equal("suspend repl input")
expect(suspendResumeRoute("resume")).to_equal("resume repl input")
expect(appendStdoutRoute(false, "out")).to_equal("buffer stdout until idle")
expect(appendStdoutRoute(true, "out")).to_equal("append stdout when idle")
expect(appendStdoutRoute(true, "")).to_equal("skip empty stdout")
```

</details>

#### should check modeled source floor

- should check modeled source floor
- Read source line helper
   - Expected: replSourceLinesModeled() equals `5005`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should check modeled source floor")
step("Read source line helper")
expect(replSourceLinesModeled()).to_equal(5005)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `4cb47491112cc0618e0c5f23b9ad11b7a2be2d571fcf53fdf78ca5fe9c36afc4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4cb47491112cc0618e0c5f23b9ad11b7a2be2d571fcf53fdf78ca5fe9c36afc4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4cb47491112cc0618e0c5f23b9ad11b7a2be2d571fcf53fdf78ca5fe9c36afc4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/03_system/tools/llm/claude_full/screens/REPL_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/screens/REPL_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/screens/REPL_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/screens/REPL_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/screens/REPL_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/screens/REPL_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model transcript search footer and title routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/screens/REPL_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model transcript search footer and title routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/screens/REPL_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model query command permission and queue routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/screens/REPL_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model query command permission and queue routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/screens/REPL_spec.spl:72:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model exit transcript suspend and stdout routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/screens/REPL_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model exit transcript suspend and stdout routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/screens/REPL_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should check modeled source floor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
