# Claude Full Terminal Querier

> Purpose: should build terminal query request sequences

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Terminal Querier

Purpose: should build terminal query request sequences

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/terminal-querier_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should build terminal query request sequences
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Terminal Querier

Checks terminal query builders and DA1 sentinel queue draining.

## Scenarios

### Claude full TerminalQuerier

#### should build terminal query request sequences

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should build terminal query request sequences
- Verify: should build terminal query request sequences
- Build core terminal query escape sequences
   - Expected: decrqm(2026).request equals `\u001B[?2026$p`
   - Expected: da1().request equals `\u001B[c`
   - Expected: da2().request equals `\u001B[>c`
   - Expected: kittyKeyboard().request equals `\u001B[?u`
   - Expected: cursorPosition().request equals `\u001B[?6n`
   - Expected: oscColor(11).request equals `\u001B]11;?\u0007`
   - Expected: xtversion().request equals `\u001B[>0q`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should build terminal query request sequences")
step("Verify: should build terminal query request sequences")
# @req: REQ-TOOLS-TermQuer-001
step("Build core terminal query escape sequences")
expect(decrqm(2026).request).to_equal("\u001B[?2026$p")
expect(da1().request).to_equal("\u001B[c")
expect(da2().request).to_equal("\u001B[>c")
expect(kittyKeyboard().request).to_equal("\u001B[?u")
expect(cursorPosition().request).to_equal("\u001B[?6n")
expect(oscColor(11).request).to_equal("\u001B]11;?\u0007")
expect(xtversion().request).to_equal("\u001B[>0q")
```

</details>

#### should match response types with mode and code constraints

- should match response types with mode and code constraints
- Verify: should match response types with mode and code constraints
- Check query matcher behavior
   - Expected: queryMatches(decrqm(2026), decrpmResponse(2026)) is true
   - Expected: queryMatches(decrqm(2026), decrpmResponse(2027)) is false
   - Expected: queryMatches(oscColor(11), oscResponse(11)) is true
   - Expected: queryMatches(oscColor(10), oscResponse(11)) is false
   - Expected: queryMatches(da1(), response("da1")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should match response types with mode and code constraints")
step("Verify: should match response types with mode and code constraints")
# @req: REQ-TOOLS-TermQuer-001
step("Check query matcher behavior")
expect(queryMatches(decrqm(2026), decrpmResponse(2026))).to_equal(true)
expect(queryMatches(decrqm(2026), decrpmResponse(2027))).to_equal(false)
expect(queryMatches(oscColor(11), oscResponse(11))).to_equal(true)
expect(queryMatches(oscColor(10), oscResponse(11))).to_equal(false)
expect(queryMatches(da1(), response("da1"))).to_equal(true)
```

</details>

#### should send queries and resolve matching responses out of queue order

- should send queries and resolve matching responses out of queue order
- Verify: should send queries and resolve matching responses out of queue order
- Resolve the first matching query even when not at the head
   - Expected: querier.pendingCount() equals `1`
   - Expected: querier.resolved[0] equals `osc:osc`
   - Expected: querier.writtenText() equals `\u001B[?2026$p\u001B]11;?\u0007`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should send queries and resolve matching responses out of queue order")
step("Verify: should send queries and resolve matching responses out of queue order")
# @req: REQ-TOOLS-TermQuer-001
step("Resolve the first matching query even when not at the head")
val querier = TerminalQuerier.new()
querier.send(decrqm(2026))
querier.send(oscColor(11))
querier.onResponse(oscResponse(11))
expect(querier.pendingCount()).to_equal(1)  # oracle: value fixed by the spec contract
expect(querier.resolved[0]).to_equal("osc:osc")
expect(querier.writtenText()).to_equal("\u001B[?2026$p\u001B]11;?\u0007")
```

</details>

#### should flush with a DA1 sentinel and mark previous queries unsupported

- should flush with a DA1 sentinel and mark previous queries unsupported
- Verify: should flush with a DA1 sentinel and mark previous queries unsupported
- Flush a query batch and receive DA1
   - Expected: querier.resolved equals `["decrpm:undefined", "sentinel:resolved"]`
   - Expected: querier.pendingCount() equals `1`
   - Expected: querier.queue[0].query.matchType equals `kittyKeyboard`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should flush with a DA1 sentinel and mark previous queries unsupported")
step("Verify: should flush with a DA1 sentinel and mark previous queries unsupported")
# @req: REQ-TOOLS-TermQuer-001
step("Flush a query batch and receive DA1")
val querier = TerminalQuerier.new()
querier.send(decrqm(2026))
querier.flush()
querier.send(kittyKeyboard())
querier.onResponse(response("da1"))
expect(querier.resolved).to_equal(["decrpm:undefined", "sentinel:resolved"])
expect(querier.pendingCount()).to_equal(1)  # oracle: value fixed by the spec contract
expect(querier.queue[0].query.matchType).to_equal("kittyKeyboard")
```

</details>

#### should let explicit DA1 queries consume the first DA1 before sentinel

- should let explicit DA1 queries consume the first DA1 before sentinel
- Verify: should let explicit DA1 queries consume the first DA1 before sentinel
- Send explicit DA1 and then flush
   - Expected: querier.resolved[0] equals `da1:da1`
   - Expected: querier.pendingCount() equals `1`
   - Expected: querier.resolved[1] equals `sentinel:resolved`
   - Expected: querier.pendingCount() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should let explicit DA1 queries consume the first DA1 before sentinel")
step("Verify: should let explicit DA1 queries consume the first DA1 before sentinel")
# @req: REQ-TOOLS-TermQuer-001
step("Send explicit DA1 and then flush")
val querier = TerminalQuerier.new()
querier.send(da1())
querier.flush()
querier.onResponse(response("da1"))
expect(querier.resolved[0]).to_equal("da1:da1")
expect(querier.pendingCount()).to_equal(1)  # oracle: value fixed by the spec contract
querier.onResponse(response("da1"))
expect(querier.resolved[1]).to_equal("sentinel:resolved")
expect(querier.pendingCount()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### should ignore unsolicited non-sentinel responses

- should ignore unsolicited non-sentinel responses
- Verify: should ignore unsolicited non-sentinel responses
- Dispatch a response with no pending match
   - Expected: querier.resolved.len() equals `0`
   - Expected: querier.pendingCount() equals `0`
   - Expected: terminalQuerierSourceLinesModeled() equals `212`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should ignore unsolicited non-sentinel responses")
step("Verify: should ignore unsolicited non-sentinel responses")
# @req: REQ-TOOLS-TermQuer-001
step("Dispatch a response with no pending match")
val querier = TerminalQuerier.new()
querier.onResponse(response("xtversion"))
expect(querier.resolved.len()).to_equal(0)  # oracle: value fixed by the spec contract
expect(querier.pendingCount()).to_equal(0)  # oracle: value fixed by the spec contract
expect(terminalQuerierSourceLinesModeled()).to_equal(212)  # oracle: value fixed by the spec contract
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
- `REQ-TOOLS-TermQuer-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d93e485047c753a01a74c89e182cbd97eec9bccb20b52e144b14f5f7dd03e64b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d93e485047c753a01a74c89e182cbd97eec9bccb20b52e144b14f5f7dd03e64b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d93e485047c753a01a74c89e182cbd97eec9bccb20b52e144b14f5f7dd03e64b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/ink/terminal-querier_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/ink/terminal-querier_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/ink/terminal-querier_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/ink/terminal-querier_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/ink/terminal-querier_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should build terminal query request sequences' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/terminal-querier_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should build terminal query request sequences' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/terminal-querier_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should match response types with mode and code constraints' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/terminal-querier_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should match response types with mode and code constraints' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/terminal-querier_spec.spl:50:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should send queries and resolve matching responses out of queue order' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/terminal-querier_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should send queries and resolve matching responses out of queue order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/terminal-querier_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should flush with a DA1 sentinel and mark previous queries unsupported' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/terminal-querier_spec.spl:79:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should let explicit DA1 queries consume the first DA1 before sentinel' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/terminal-querier_spec.spl:95:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should ignore unsolicited non-sentinel responses' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
