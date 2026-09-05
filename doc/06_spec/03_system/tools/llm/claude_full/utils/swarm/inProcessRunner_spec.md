# Claude Full In-Process Swarm Runner Slice

> Focused Simple coverage for pure in-process teammate runner helpers from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full In-Process Swarm Runner Slice

Focused Simple coverage for pure in-process teammate runner helpers from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/swarm/inProcessRunner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused Simple coverage for pure in-process teammate runner helpers from
utils/swarm/inProcessRunner.ts.

## Scenarios

### Claude full in-process runner parity

#### should model teammate message formatting

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model teammate message formatting
- Check teammate XML wrapper
   - Expected: formatAsTeammateMessageRoute("t1", "", "", "hello") equals `<teammate-message teammate_id="t1">\nhello\n</teammate-message>`
   - Expected: formatAsTeammateMessageRoute("t1", "blue", "", "hello") equals `<teammate-message teammate_id="t1" color="blue">\nhello\n</teammate-message>`
   - Expected: formatAsTeammateMessageRoute("t1", "", "summary", "hello") equals `<teammate-message teammate_id="t1" summary="summary">\nhello\n</teammate-mess... (full value in folded executable source)`
   - Expected: formatAsTeammateMessageRoute("t1", "blue", "summary", "line1\nline2") equals `<teammate-message teammate_id="t1" color="blue" summary="summary">\nline1\nli... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model teammate message formatting")
step("Check teammate XML wrapper")
expect(formatAsTeammateMessageRoute("t1", "", "", "hello")).to_equal("<teammate-message teammate_id=\"t1\">\nhello\n</teammate-message>")
expect(formatAsTeammateMessageRoute("t1", "blue", "", "hello")).to_equal("<teammate-message teammate_id=\"t1\" color=\"blue\">\nhello\n</teammate-message>")
expect(formatAsTeammateMessageRoute("t1", "", "summary", "hello")).to_equal("<teammate-message teammate_id=\"t1\" summary=\"summary\">\nhello\n</teammate-message>")
expect(formatAsTeammateMessageRoute("t1", "blue", "summary", "line1\nline2")).to_equal("<teammate-message teammate_id=\"t1\" color=\"blue\" summary=\"summary\">\nline1\nline2\n</teammate-message>")
```

</details>

#### should model available task selection

- should model available task selection
- Check task availability
   - Expected: findAvailableTaskRoute("pending", "", 0) is true
   - Expected: findAvailableTaskRoute("completed", "", 0) is false
   - Expected: findAvailableTaskRoute("pending", "agent-1", 0) is false
   - Expected: findAvailableTaskRoute("pending", "", 1) is false
   - Expected: findAvailableTaskIndexRoute(2) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model available task selection")
step("Check task availability")
expect(findAvailableTaskRoute("pending", "", 0)).to_equal(true)
expect(findAvailableTaskRoute("completed", "", 0)).to_equal(false)
expect(findAvailableTaskRoute("pending", "agent-1", 0)).to_equal(false)
expect(findAvailableTaskRoute("pending", "", 1)).to_equal(false)
expect(findAvailableTaskIndexRoute(2)).to_equal(2)
```

</details>

#### should model task prompt formatting

- should model task prompt formatting
- Check prompt formatting
   - Expected: formatTaskAsPromptRoute("7", "") equals `Complete all open tasks. Start with task #7.`
   - Expected: inProcessRunnerSourceLinesModeled() equals `1553`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model task prompt formatting")
step("Check prompt formatting")
expect(formatTaskAsPromptRoute("7", "Do the thing")).to_start_with("Complete all open tasks. Start with task #7.")
expect(formatTaskAsPromptRoute("7", "Do the thing")).to_contain("Do the thing")
expect(formatTaskAsPromptRoute("7", "")).to_equal("Complete all open tasks. Start with task #7.")
expect(inProcessRunnerSourceLinesModeled()).to_equal(1553)
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

- Canonical SPipe generation for source `f819a09363e18438fdd2f419d2f12672c20f333f2e473b16bba6ff5077dbf159`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f819a09363e18438fdd2f419d2f12672c20f333f2e473b16bba6ff5077dbf159`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f819a09363e18438fdd2f419d2f12672c20f333f2e473b16bba6ff5077dbf159`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/swarm/inProcessRunner_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/swarm/inProcessRunner_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/swarm/inProcessRunner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/swarm/inProcessRunner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/swarm/inProcessRunner_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/swarm/inProcessRunner_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model teammate message formatting' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/swarm/inProcessRunner_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model teammate message formatting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/swarm/inProcessRunner_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model available task selection' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/swarm/inProcessRunner_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model available task selection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/swarm/inProcessRunner_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model task prompt formatting' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/swarm/inProcessRunner_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model task prompt formatting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
