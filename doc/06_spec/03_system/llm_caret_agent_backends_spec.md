# LLM Caret Agent Backends (Claude + Codex + Gemini + Kimi)

> Proves the LLM Caret agent manager can launch, poll, and stop an agent process

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Agent Backends (Claude + Codex + Gemini + Kimi)

Proves the LLM Caret agent manager can launch, poll, and stop an agent process

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/llm_caret_agent_teams.md (agent launch contract) |
| Source | `test/03_system/llm_caret_agent_backends_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Proves the LLM Caret agent manager can launch, poll, and stop an agent process
through the Claude, Codex, Gemini, and Kimi CLI wrapper contracts.
Audience: anyone changing `agent_plan.spl` argv construction or
`agent_runtime.spl` spawn/status/kill paths.

## Scope and Preconditions

Runs the real spawn/poll/kill path end-to-end using `/bin/echo` as the backend
binary, so no paid API call and no installed claude/codex CLI is required. The
argv contract itself is asserted separately, so a stub binary does not weaken
the backend-shape oracle. Requires a POSIX `/bin/echo`.

## Primary Workflow

Build a launch plan per provider, assert its argv contract, spawn it, poll its
status (running or already exited — echo is fast), then stop it.

## Compatibility and Limitations

Live-CLI conversation behavior is out of scope; see
`test/03_system/llm_caret_live_comprehensive_spec.spl` for the paid live gate.

## Scenarios

### LLM Caret agent backends (claude + codex + gemini + kimi)

#### builds the claude argv contract

- builds the claude argv contract
- Plan a claude_cli launch and assert the -p/--output-format json shape
   - Expected: plan.argv[0] equals `-p`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds the claude argv contract")
step("Plan a claude_cli launch and assert the -p/--output-format json shape")
val plan = build_agent_launch_plan(backend_request("claude_cli"))
expect(plan.argv[0]).to_equal("-p")
expect(plan.argv).to_contain("--output-format")
expect(plan.argv).to_contain("json")
```

</details>

#### builds the codex argv contract

- builds the codex argv contract
- Plan a codex launch and assert the exec <prompt> shape
   - Expected: plan.argv[0] equals `exec`
   - Expected: plan.argv.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds the codex argv contract")
step("Plan a codex launch and assert the exec <prompt> shape")
val plan = build_agent_launch_plan(backend_request("codex"))
expect(plan.argv[0]).to_equal("exec")
expect(plan.argv.len()).to_equal(2)
```

</details>

#### launches, polls, and stops a claude-backed agent process

- launches, polls, and stops a claude-backed agent process


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("launches, polls, and stops a claude-backed agent process")
launch_poll_stop("sys-claude", "claude_cli", "/bin/echo", "", "", "")
```

</details>

#### launches, polls, and stops a codex-backed agent process

- launches, polls, and stops a codex-backed agent process


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("launches, polls, and stops a codex-backed agent process")
launch_poll_stop("sys-codex", "codex", "", "/bin/echo", "", "")
```

</details>

#### launches, polls, and stops a gemini-backed agent process

- launches, polls, and stops a gemini-backed agent process


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("launches, polls, and stops a gemini-backed agent process")
launch_poll_stop("sys-gemini", "gemini", "", "", "/bin/echo", "")
```

</details>

#### launches, polls, and stops a kimi-backed agent process

- launches, polls, and stops a kimi-backed agent process


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("launches, polls, and stops a kimi-backed agent process")
launch_poll_stop("sys-kimi", "kimi", "", "", "", "/bin/echo")
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

- **Requirements:** `doc/02_requirements/feature/llm_caret_agent_teams.md (agent launch contract)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-BACKEND-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6dee3d3e148cda72991412298cf0e9dbd2e18832943159d8973b4c83c30221b3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6dee3d3e148cda72991412298cf0e9dbd2e18832943159d8973b4c83c30221b3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6dee3d3e148cda72991412298cf0e9dbd2e18832943159d8973b4c83c30221b3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/llm_caret_agent_backends_spec.spl
mirror: doc/06_spec/03_system/llm_caret_agent_backends_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/llm_caret_agent_backends_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/llm_caret_agent_backends_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/llm_caret_agent_backends_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/llm_caret_agent_backends_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/llm_caret_agent_backends_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds the claude argv contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/llm_caret_agent_backends_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds the codex argv contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/llm_caret_agent_backends_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'launches, polls, and stops a claude-backed agent process' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
