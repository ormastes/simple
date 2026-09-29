# Claude Full Query Slice

> Purpose: should model query envelope routes

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Query Slice

Purpose: should model query envelope routes

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/query_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should model query envelope routes
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Query Slice

Focused Simple coverage for the public query envelope and missing tool-result
helpers from query.ts.

## Scenarios

### Claude full query parity

#### should model query envelope routes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model query envelope routes
- Verify: should model query envelope routes
- Check query envelope
   - Expected: params.prompt equals `hello`
   - Expected: params.maxTurns equals `3`
   - Expected: queryEnvelopeRoute("completed") equals `stream_request_start|completed`
   - Expected: queryEnvelopeRoute("model_error") equals `stream_request_start|model_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model query envelope routes")
step("Verify: should model query envelope routes")
# @req: REQ-TOOLS-Quer-001
step("Check query envelope")
val params = QueryParams.new("hello", 3)
expect(params.prompt).to_equal("hello")
expect(params.maxTurns).to_equal(3)  # oracle: value fixed by the spec contract
expect(queryEnvelopeRoute("completed")).to_equal("stream_request_start|completed")
expect(queryEnvelopeRoute("model_error")).to_equal("stream_request_start|model_error")
```

</details>

#### should model withheld max output token errors

- should model withheld max output token errors
- Verify: should model withheld max output token errors
- Check withheld max output tokens
   - Expected: isWithheldMaxOutputTokensRoute(false, "") is false
   - Expected: isWithheldMaxOutputTokensRoute(true, "max_output_tokens") is true
   - Expected: isWithheldMaxOutputTokensRoute(true, "rate_limit") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model withheld max output token errors")
step("Verify: should model withheld max output token errors")
# @req: REQ-TOOLS-Quer-001
step("Check withheld max output tokens")
expect(isWithheldMaxOutputTokensRoute(false, "")).to_equal(false)
expect(isWithheldMaxOutputTokensRoute(true, "max_output_tokens")).to_equal(true)
expect(isWithheldMaxOutputTokensRoute(true, "rate_limit")).to_equal(false)
```

</details>

#### should model missing tool result blocks

- should model missing tool result blocks
- Verify: should model missing tool result blocks
- Check missing tool result routes
   - Expected: yieldMissingToolResultBlocksRoute(0, "missing", "a1") equals `none`
   - Expected: yieldMissingToolResultBlocksRoute(2, "missing", "a1") equals `user tool_result error missing source a1 count 2`
   - Expected: missingToolResultItemRoute("missing", "a1") equals `type:user tool_result is_error:true content:missing source:a1`
   - Expected: querySourceLinesModeled() equals `1729`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model missing tool result blocks")
step("Verify: should model missing tool result blocks")
# @req: REQ-TOOLS-Quer-001
step("Check missing tool result routes")
expect(yieldMissingToolResultBlocksRoute(0, "missing", "a1")).to_equal("none")
expect(yieldMissingToolResultBlocksRoute(2, "missing", "a1")).to_equal("user tool_result error missing source a1 count 2")
expect(missingToolResultItemRoute("missing", "a1")).to_equal("type:user tool_result is_error:true content:missing source:a1")
expect(querySourceLinesModeled()).to_equal(1729)  # oracle: value fixed by the spec contract
```

</details>

#### should continue below the token budget completion threshold

- should continue below the token budget completion threshold
- Verify: should continue below the token budget completion threshold
- Check budget continuation
   - Expected: decision.action equals `continue`
   - Expected: decision.continuationCount equals `1`
   - Expected: decision.pct equals `50`
   - Expected: decision.nudgeMessage equals `Stopped at 50% of token target (50,000 / 100,000). Keep working \u2014 do not... (full value in folded executable source)`
   - Expected: tracker.lastGlobalTurnTokens equals `50000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should continue below the token budget completion threshold")
step("Verify: should continue below the token budget completion threshold")
# @req: REQ-TOOLS-Quer-001
step("Check budget continuation")
val tracker = BudgetTracker.new(1000)
val decision = tracker.check("", 100000, 50000, 1100)
expect(decision.action).to_equal("continue")
expect(decision.continuationCount).to_equal(1)  # oracle: value fixed by the spec contract
expect(decision.pct).to_equal(50)  # oracle: value fixed by the spec contract
expect(decision.nudgeMessage).to_equal("Stopped at 50% of token target (50,000 / 100,000). Keep working \u2014 do not summarize.")
expect(tracker.lastGlobalTurnTokens).to_equal(50000)  # oracle: value fixed by the spec contract
```

</details>

#### should stop near the token budget after at least one continuation

- should stop near the token budget after at least one continuation
- Verify: should stop near the token budget after at least one continuation
- Check completion event
   - Expected: decision.action equals `stop`
   - Expected: decision.hasCompletionEvent is true
   - Expected: decision.diminishingReturns is false
   - Expected: decision.durationMs equals `600`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should stop near the token budget after at least one continuation")
step("Verify: should stop near the token budget after at least one continuation")
# @req: REQ-TOOLS-Quer-001
step("Check completion event")
val tracker = BudgetTracker.new(1000)
tracker.check("", 1000, 500, 1100)
val decision = tracker.check("", 1000, 900, 1600)
expect(decision.action).to_equal("stop")
expect(decision.hasCompletionEvent).to_equal(true)
expect(decision.diminishingReturns).to_equal(false)
expect(decision.durationMs).to_equal(600)  # oracle: value fixed by the spec contract
```

</details>

#### should stop without an event for agent or missing budgets

- should stop without an event for agent or missing budgets
- Verify: should stop without an event for agent or missing budgets
- Check skipped budget gates
   - Expected: BudgetTracker.new(0).check("agent-1", 1000, 100, 10).hasCompletionEvent is false
   - Expected: BudgetTracker.new(0).check("", 0, 100, 10).action equals `stop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should stop without an event for agent or missing budgets")
step("Verify: should stop without an event for agent or missing budgets")
# @req: REQ-TOOLS-Quer-001
step("Check skipped budget gates")
expect(BudgetTracker.new(0).check("agent-1", 1000, 100, 10).hasCompletionEvent).to_equal(false)
expect(BudgetTracker.new(0).check("", 0, 100, 10).action).to_equal("stop")
```

</details>

#### should stop on repeated small token deltas

- should stop on repeated small token deltas
- Verify: should stop on repeated small token deltas
- Check diminishing returns
   - Expected: decision.action equals `stop`
   - Expected: decision.hasCompletionEvent is true
   - Expected: decision.diminishingReturns is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should stop on repeated small token deltas")
step("Verify: should stop on repeated small token deltas")
# @req: REQ-TOOLS-Quer-001
step("Check diminishing returns")
val tracker = BudgetTracker.new(1000)
tracker.check("", 10000, 1000, 1100)
tracker.check("", 10000, 1300, 1200)
tracker.check("", 10000, 1500, 1300)
val decision = tracker.check("", 10000, 1600, 1400)
expect(decision.action).to_equal("stop")
expect(decision.hasCompletionEvent).to_equal(true)
expect(decision.diminishingReturns).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Quer-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9ebdaee3e328ad8b66f9e7b683d5afb135baa9389bc25dddc9884d6d3574a239`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9ebdaee3e328ad8b66f9e7b683d5afb135baa9389bc25dddc9884d6d3574a239`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9ebdaee3e328ad8b66f9e7b683d5afb135baa9389bc25dddc9884d6d3574a239`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/query_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/query_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/query_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/query_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/query_spec.spl:25:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model query envelope routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/query_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model query envelope routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/query_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model withheld max output token errors' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/query_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model withheld max output token errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/query_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model missing tool result blocks' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/query_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model missing tool result blocks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/query_spec.spl:58:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should continue below the token budget completion threshold' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/query_spec.spl:72:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should stop near the token budget after at least one continuation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/query_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should stop without an event for agent or missing budgets' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
