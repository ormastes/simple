# Claude Full Ink Main Slice

> Focused coverage for ink.tsx lifecycle, alt-screen, deferred render, console,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Ink Main Slice

Focused coverage for ink.tsx lifecycle, alt-screen, deferred render, console,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/ink_main_slice_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused coverage for ink.tsx lifecycle, alt-screen, deferred render, console,
stdin, selection, and event dispatch parity routes.

## Scenarios

### Claude full Ink main parity

#### should model options class lifecycle and alt screen routes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model options class lifecycle and alt screen routes
- Check options and instance lifecycle
   - Expected: options.exitOnCtrlC is true
   - Expected: options.patchConsole is true
   - Expected: options.hasOnFrame is true
   - Expected: ink.renderRoute(true) equals `mount or update reconciler root`
   - Expected: ink.isMounted is true
   - Expected: ink.repaintRoute(false) equals `repaint invalidates prev frame render`
   - Expected: ink.repaintRoute(true) equals `forceRedraw reset framebuffer displayCursor erase render`
   - Expected: ink.setAltScreenActiveRoute(true, true) equals `enter alt screen enable mouse tracking`
   - Expected: ink.altScreenActive is true
   - Expected: ink.pauseRoute() equals `flush reconciler render once then pause`
   - Expected: ink.isPaused is true
   - Expected: ink.resumeRoute() equals `resume then render immediately`
   - Expected: ink.unmountRoute() equals `restore terminal and unmount root`
   - Expected: ink.isMounted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model options class lifecycle and alt screen routes")
step("Check options and instance lifecycle")
val options = Options.new(true, true, false, true)
expect(options.exitOnCtrlC).to_equal(true)
expect(options.patchConsole).to_equal(true)
expect(options.hasOnFrame).to_equal(true)
val ink = Ink.new()
expect(ink.renderRoute(true)).to_equal("mount or update reconciler root")
expect(ink.isMounted).to_equal(true)
expect(ink.repaintRoute(false)).to_equal("repaint invalidates prev frame render")
expect(ink.repaintRoute(true)).to_equal("forceRedraw reset framebuffer displayCursor erase render")
expect(ink.setAltScreenActiveRoute(true, true)).to_equal("enter alt screen enable mouse tracking")
expect(ink.altScreenActive).to_equal(true)
expect(ink.pauseRoute()).to_equal("flush reconciler render once then pause")
expect(ink.isPaused).to_equal(true)
expect(ink.resumeRoute()).to_equal("resume then render immediately")
expect(ink.unmountRoute()).to_equal("restore terminal and unmount root")
expect(ink.isMounted).to_equal(false)
```

</details>

#### should model deferred render console callback and stdin helpers

- should model deferred render console callback and stdin helpers
- Check helpers exported by ink.tsx
   - Expected: makeAltScreenParkPatch(3) equals `\x1b[3;1H`
   - Expected: makeAltScreenParkPatch(0) equals `\x1b[H`
   - Expected: deferredRenderRoute(false, true, false) equals `queue microtask then schedule deferred frame`
   - Expected: deferredRenderRoute(true, true, false) equals `coalesce scheduled render`
   - Expected: deferredRenderRoute(false, true, true) equals `defer while paused`
   - Expected: deferredRenderRoute(false, false, false) equals `skip unmounted`
   - Expected: blank(4) equals `    `
   - Expected: toDebug("a b") equals `a b`
   - Expected: toError("err") equals `err`
   - Expected: interceptRoute(false, "stdout") equals `leave console alone`
   - Expected: interceptRoute(true, "stderr") equals `capture stderr console`
   - Expected: interceptWriteRoute(true, true, false, false) equals `passthrough original writer`
   - Expected: interceptWriteRoute(false, true, false, false) equals `mark frame contaminated schedule render`
   - Expected: interceptWriteRoute(false, true, false, true) equals `mark frame contaminated no schedule`
   - Expected: callbackRoute("frame", false) equals `call onFrame with timing metadata`
   - Expected: callbackRoute("debug", true) equals `skip callback after exit`
   - Expected: callbackFinallyRoute(true) equals `callback exactly once in finally`
   - Expected: interceptCallbackRoute(true, true) equals `no callback passthrough`
   - Expected: interceptCallbackRoute(false, true) equals `stderr callback cleanup exactly once`
   - Expected: drainStdinRoute(false, true, false) equals `noop non tty`
   - Expected: drainStdinRoute(true, true, false) equals `drain buffered tty input`
   - Expected: drainStdinRoute(true, true, true) equals `idempotent drain`
   - Expected: drainStdinPlatformRoute("win32", 0, true) equals `noop win32`
   - Expected: drainStdinPlatformRoute("linux", 64, true) equals `bounded 64 reads cleanup`
   - Expected: blankStateRoute(3) equals `viewport rows plus one cursor y 0 contaminated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model deferred render console callback and stdin helpers")
step("Check helpers exported by ink.tsx")
expect(makeAltScreenParkPatch(3)).to_equal("\x1b[3;1H")
expect(makeAltScreenParkPatch(0)).to_equal("\x1b[H")
expect(deferredRenderRoute(false, true, false)).to_equal("queue microtask then schedule deferred frame")
expect(deferredRenderRoute(true, true, false)).to_equal("coalesce scheduled render")
expect(deferredRenderRoute(false, true, true)).to_equal("defer while paused")
expect(deferredRenderRoute(false, false, false)).to_equal("skip unmounted")
expect(blank(4)).to_equal("    ")
expect(toDebug("a b")).to_equal("a b")
expect(toError("err")).to_equal("err")
expect(interceptRoute(false, "stdout")).to_equal("leave console alone")
expect(interceptRoute(true, "stderr")).to_equal("capture stderr console")
expect(interceptWriteRoute(true, true, false, false)).to_equal("passthrough original writer")
expect(interceptWriteRoute(false, true, false, false)).to_equal("mark frame contaminated schedule render")
expect(interceptWriteRoute(false, true, false, true)).to_equal("mark frame contaminated no schedule")
expect(callbackRoute("frame", false)).to_equal("call onFrame with timing metadata")
expect(callbackRoute("debug", true)).to_equal("skip callback after exit")
expect(callbackFinallyRoute(true)).to_equal("callback exactly once in finally")
expect(interceptCallbackRoute(true, true)).to_equal("no callback passthrough")
expect(interceptCallbackRoute(false, true)).to_equal("stderr callback cleanup exactly once")
expect(drainStdinRoute(false, true, false)).to_equal("noop non tty")
expect(drainStdinRoute(true, true, false)).to_equal("drain buffered tty input")
expect(drainStdinRoute(true, true, true)).to_equal("idempotent drain")
expect(drainStdinPlatformRoute("win32", 0, true)).to_equal("noop win32")
expect(drainStdinPlatformRoute("linux", 64, true)).to_equal("bounded 64 reads cleanup")
expect(blankStateRoute(3)).to_equal("viewport rows plus one cursor y 0 contaminated")
```

</details>

#### should model lifecycle input selection and event dispatch

- should model lifecycle input selection and event dispatch
- Check orchestration routes
   - Expected: lifecycleRoute("render", false, false) equals `mount update provider tree`
   - Expected: lifecycleRoute("unmount", true, false) equals `synchronous restore cleanup`
   - Expected: lifecycleRoute("resize", true, false) equals `update rows cols rerender`
   - Expected: lifecycleRoute("forceRedraw", true, false) equals `invalidate prev frame repaint`
   - Expected: lifecycleRoute("noop", true, true) equals `paused lifecycle no write`
   - Expected: inputRoute(true, true, "\x03") equals `let app exit`
   - Expected: inputRoute(true, false, "x") equals `dispatch keyboard input`
   - Expected: inputRoute(false, false, "x") equals `ignore inactive input`
   - Expected: resizeRoute(false, true, false) equals `same size resize no op`
   - Expected: resizeRoute(true, true, false) equals `resize alt screen reset buffers needs erase rerender`
   - Expected: resizeRoute(true, false, true) equals `resize while paused update tree`
   - Expected: selectionRouteInk("copy", true) equals `copy selection and clear`
   - Expected: selectionRouteInk("copyNoClear", true) equals `copy selection keep state`
   - Expected: selectionRouteInk("clear", false) equals `clear text selection`
   - Expected: eventDispatchRoute("click", false) equals `focus then bubble click`
   - Expected: eventDispatchRoute("hover", false) equals `dispatch hover enter leave`
   - Expected: eventDispatchRoute("keyboard", false) equals `dispatch focused keyboard`
   - Expected: eventDispatchRoute("click", true) equals `stop dispatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model lifecycle input selection and event dispatch")
step("Check orchestration routes")
expect(lifecycleRoute("render", false, false)).to_equal("mount update provider tree")
expect(lifecycleRoute("unmount", true, false)).to_equal("synchronous restore cleanup")
expect(lifecycleRoute("resize", true, false)).to_equal("update rows cols rerender")
expect(lifecycleRoute("forceRedraw", true, false)).to_equal("invalidate prev frame repaint")
expect(lifecycleRoute("noop", true, true)).to_equal("paused lifecycle no write")
expect(inputRoute(true, true, "\x03")).to_equal("let app exit")
expect(inputRoute(true, false, "x")).to_equal("dispatch keyboard input")
expect(inputRoute(false, false, "x")).to_equal("ignore inactive input")
expect(resizeRoute(false, true, false)).to_equal("same size resize no op")
expect(resizeRoute(true, true, false)).to_equal("resize alt screen reset buffers needs erase rerender")
expect(resizeRoute(true, false, true)).to_equal("resize while paused update tree")
expect(selectionRouteInk("copy", true)).to_equal("copy selection and clear")
expect(selectionRouteInk("copyNoClear", true)).to_equal("copy selection keep state")
expect(selectionRouteInk("clear", false)).to_equal("clear text selection")
expect(eventDispatchRoute("click", false)).to_equal("focus then bubble click")
expect(eventDispatchRoute("hover", false)).to_equal("dispatch hover enter leave")
expect(eventDispatchRoute("keyboard", false)).to_equal("dispatch focused keyboard")
expect(eventDispatchRoute("click", true)).to_equal("stop dispatch")
```

</details>

#### should check modeled TypeScript source floor

- should check modeled TypeScript source floor
- Read source line helper
   - Expected: inkSourceLinesModeled() equals `1722`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should check modeled TypeScript source floor")
step("Read source line helper")
expect(inkSourceLinesModeled()).to_equal(1722)
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

- Canonical SPipe generation for source `6746358dfe84fd5d80222216669ff9f3bdfa81d15dcccad5c388b42225406ea5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6746358dfe84fd5d80222216669ff9f3bdfa81d15dcccad5c388b42225406ea5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6746358dfe84fd5d80222216669ff9f3bdfa81d15dcccad5c388b42225406ea5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/03_system/tools/llm/claude_full/components/ink_main_slice_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/ink_main_slice_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/ink_main_slice_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/ink_main_slice_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/ink_main_slice_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/ink_main_slice_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model options class lifecycle and alt screen routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/ink_main_slice_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model options class lifecycle and alt screen routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/ink_main_slice_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model deferred render console callback and stdin helpers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/ink_main_slice_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model deferred render console callback and stdin helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/ink_main_slice_spec.spl:70:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model lifecycle input selection and event dispatch' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/ink_main_slice_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model lifecycle input selection and event dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/ink_main_slice_spec.spl:93:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should check modeled TypeScript source floor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
