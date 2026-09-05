# Claude Full combined abort signal

> Pure Simple coverage for combined abort signal lifecycle modeling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full combined abort signal

Pure Simple coverage for combined abort signal lifecycle modeling.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/combined_abort_signal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for combined abort signal lifecycle modeling.

## Scenarios

### Claude full combined abort signal

#### aborts immediately when either input signal is already aborted

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- aborts immediately when either input signal is already aborted
- Check immediate abort
   - Expected: result.aborted is true
   - Expected: result.listenerCount equals `0`
   - Expected: result.timerActive is false
   - Expected: result.cleanupNeeded is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aborts immediately when either input signal is already aborted")
step("Check immediate abort")
val result = createCombinedAbortSignal(true, false, true, true, 1000)
expect(result.aborted).to_equal(true)
expect(result.listenerCount).to_equal(0)
expect(result.timerActive).to_equal(false)
expect(result.cleanupNeeded).to_equal(false)
```

</details>

#### registers listeners and timeout cleanup for active inputs

- registers listeners and timeout cleanup for active inputs
- Check active composition
   - Expected: result.aborted is false
   - Expected: result.listenerCount equals `2`
   - Expected: result.timerActive is true
   - Expected: cleaned.listenerCount equals `0`
   - Expected: cleaned.timerActive is false
   - Expected: cleaned.cleanupNeeded is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("registers listeners and timeout cleanup for active inputs")
step("Check active composition")
val result = createCombinedAbortSignal(true, false, true, false, 1000)
expect(result.aborted).to_equal(false)
expect(result.listenerCount).to_equal(2)
expect(result.timerActive).to_equal(true)
val cleaned = result.cleanup()
expect(cleaned.listenerCount).to_equal(0)
expect(cleaned.timerActive).to_equal(false)
expect(cleaned.cleanupNeeded).to_equal(false)
```

</details>

#### aborts from input and clears the timeout

- aborts from input and clears the timeout
- Check input abort
   - Expected: result.aborted is true
   - Expected: result.listenerCount equals `1`
   - Expected: result.timerActive is false
   - Expected: result.cleanupNeeded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aborts from input and clears the timeout")
step("Check input abort")
val result = createCombinedAbortSignal(true, false, false, false, 1000).abortFromInput()
expect(result.aborted).to_equal(true)
expect(result.listenerCount).to_equal(1)
expect(result.timerActive).to_equal(false)
expect(result.cleanupNeeded).to_equal(true)
```

</details>

#### supports timeout-only composition

- supports timeout-only composition
- Check timeout-only abort
   - Expected: result.listenerCount equals `0`
   - Expected: result.timerActive is true
   - Expected: aborted.aborted is true
   - Expected: aborted.timerActive is false
   - Expected: aborted.cleanupNeeded is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports timeout-only composition")
step("Check timeout-only abort")
val result = createCombinedAbortSignal(false, false, false, false, 50)
expect(result.listenerCount).to_equal(0)
expect(result.timerActive).to_equal(true)
val aborted = result.abortFromTimeout()
expect(aborted.aborted).to_equal(true)
expect(aborted.timerActive).to_equal(false)
expect(aborted.cleanupNeeded).to_equal(false)
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

- Canonical SPipe generation for source `3fbcab3e1f9d208c3f56c06a4c3042f3919089ae9261dbefa811ffe39a97df0e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3fbcab3e1f9d208c3f56c06a4c3042f3919089ae9261dbefa811ffe39a97df0e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3fbcab3e1f9d208c3f56c06a4c3042f3919089ae9261dbefa811ffe39a97df0e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/combined_abort_signal_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/combined_abort_signal_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/combined_abort_signal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/combined_abort_signal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/combined_abort_signal_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/combined_abort_signal_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'aborts immediately when either input signal is already aborted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/combined_abort_signal_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers listeners and timeout cleanup for active inputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/combined_abort_signal_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'aborts from input and clears the timeout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
