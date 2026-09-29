# Claude Full More Stub Commands

> Mirrors another batch of one-line Claude command index files that export hidden

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full More Stub Commands

Mirrors another batch of one-line Claude command index files that export hidden

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/more_stub_commands_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors another batch of one-line Claude command index files that export hidden
disabled stub commands.

## Scenarios

### Claude full additional stub command indexes

#### should expose hidden disabled cache, context, and good-claude commands

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose hidden disabled cache, context, and good-claude commands
- Load the first additional stub command batch


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose hidden disabled cache, context, and good-claude commands")
step("Load the first additional stub command batch")
val break_cache = breakCacheCommand()
val ctx = ctxVizCommand()
val good = goodClaudeCommand()

assert_stub(break_cache.name, break_cache.isHidden, break_cache.isEnabled())
assert_stub(ctx.name, ctx.isHidden, ctx.isEnabled())
assert_stub(good.name, good.isHidden, good.isEnabled())
```

</details>

#### should expose hidden disabled limit, oauth, and perf commands

- should expose hidden disabled limit, oauth, and perf commands
- Load the second additional stub command batch


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose hidden disabled limit, oauth, and perf commands")
step("Load the second additional stub command batch")
val mock_limits = mockLimitsCommand()
val oauth = oauthRefreshCommand()
val perf = perfIssueCommand()

assert_stub(mock_limits.name, mock_limits.isHidden, mock_limits.isEnabled())
assert_stub(oauth.name, oauth.isHidden, oauth.isEnabled())
assert_stub(perf.name, perf.isHidden, perf.isEnabled())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `84e71d388a8426661d3ed6aa20830078a7742fa819e394d910e2fe3faaf632cd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `84e71d388a8426661d3ed6aa20830078a7742fa819e394d910e2fe3faaf632cd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `84e71d388a8426661d3ed6aa20830078a7742fa819e394d910e2fe3faaf632cd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/commands/more_stub_commands_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/more_stub_commands_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/more_stub_commands_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/more_stub_commands_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/more_stub_commands_spec.spl:29:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose hidden disabled cache, context, and good-claude commands' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/more_stub_commands_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose hidden disabled cache, context, and good-claude commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/more_stub_commands_spec.spl:41:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose hidden disabled limit, oauth, and perf commands' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/more_stub_commands_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose hidden disabled limit, oauth, and perf commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
