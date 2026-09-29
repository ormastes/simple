# Agent Runtime Provider Specification

> Tests covering LLM Caret agent runtime provider hardening.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Agent Runtime Provider Specification

## Scenarios

### LLM Caret agent runtime provider hardening

#### accepts the known provider set

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts the known provider set


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts the known provider set")
assert_true(is_known_agent_provider("claude"))
assert_true(is_known_agent_provider("claude_cli"))
assert_true(is_known_agent_provider("codex"))
assert_true(is_known_agent_provider("opencode_cli"))
assert_true(is_known_agent_provider("gemini"))
assert_true(is_known_agent_provider("gemini_cli"))
assert_true(is_known_agent_provider("kimi"))
assert_true(is_known_agent_provider("kimi_cli"))
assert_true(is_known_agent_provider("team"))
assert_true(is_known_agent_provider(""))
```

</details>

#### rejects unknown providers

- rejects unknown providers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects unknown providers")
assert_false(is_known_agent_provider("bogus"))
assert_false(is_known_agent_provider("claude; rm -rf /"))
```

</details>

#### maps providers to configured binary paths

- maps providers to configured binary paths
   - Expected: agent_command_for_provider_with_all("codex", "/c", "/x", "/g", "/k", "/o") equals `/x`
   - Expected: agent_command_for_provider_with_all("gemini", "/c", "/x", "/g", "/k", "/o") equals `/g`
   - Expected: agent_command_for_provider_with_all("kimi", "/c", "/x", "/g", "/k", "/o") equals `/k`
   - Expected: agent_command_for_provider_with_all("opencode_cli", "/c", "/x", "/g", "/k", "/o") equals `/o`
   - Expected: agent_command_for_provider_with_all("claude_cli", "/c", "/x", "/g", "/k", "/o") equals `/c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("maps providers to configured binary paths")
expect(agent_command_for_provider_with_all("codex", "/c", "/x", "/g", "/k", "/o")).to_equal("/x")
expect(agent_command_for_provider_with_all("gemini", "/c", "/x", "/g", "/k", "/o")).to_equal("/g")
expect(agent_command_for_provider_with_all("kimi", "/c", "/x", "/g", "/k", "/o")).to_equal("/k")
expect(agent_command_for_provider_with_all("opencode_cli", "/c", "/x", "/g", "/k", "/o")).to_equal("/o")
expect(agent_command_for_provider_with_all("claude_cli", "/c", "/x", "/g", "/k", "/o")).to_equal("/c")
```

</details>

#### refuses to launch an unknown provider instead of falling back to claude

- refuses to launch an unknown provider instead of falling back to claude
   - Expected: proc.status equals `error`
   - Expected: proc.reason equals `unknown_provider:bogus`
   - Expected: proc.pid equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("refuses to launch an unknown provider instead of falling back to claude")
val plan = AgentLaunchPlan(provider: "bogus", mode: "agent", prompt: "p", argv: ["-p", "p"], summary: "s")
val proc = launch_agent_plan_with_all("agent-1", plan, "/bin/echo", "/bin/echo", "/bin/echo", "/bin/echo", "/bin/echo")
expect(proc.status).to_equal("error")
expect(proc.reason).to_equal("unknown_provider:bogus")
expect(proc.pid).to_equal(-1)
```

</details>

#### keeps team agent ids unique when agent_md_paths collide

- keeps team agent ids unique when agent_md_paths collide
   - Expected: team.processes.len() equals `2`
   - Expected: team.processes[0].agent_id equals `agents/dup.md`
   - Expected: team.processes[1].agent_id equals `agents/dup.md#1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps team agent ids unique when agent_md_paths collide")
val req = AgentLaunchRequest(provider: "bogus", agent_md_path: "agents/dup.md",
    skill_path: "", task_desc: "t", model: "", session_id: "", extra_args: [])
val team = launch_agent_team_with_all("team-1", [req, req], "", "", "", "", "")
expect(team.processes.len()).to_equal(2)
expect(team.processes[0].agent_id).to_equal("agents/dup.md")
expect(team.processes[1].agent_id).to_equal("agents/dup.md#1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/agent_runtime_provider_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLM Caret agent runtime provider hardening.
- LLM Caret agent runtime provider hardening

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7ed810f69a8b6a1c6a5a30b0ff45dcd5244f685f516c8d2440d851d110bfc8e1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7ed810f69a8b6a1c6a5a30b0ff45dcd5244f685f516c8d2440d851d110bfc8e1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7ed810f69a8b6a1c6a5a30b0ff45dcd5244f685f516c8d2440d851d110bfc8e1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/llm_caret/agent_runtime_provider_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/agent_runtime_provider_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/agent_runtime_provider_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/agent_runtime_provider_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/agent_runtime_provider_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/agent_runtime_provider_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the known provider set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/agent_runtime_provider_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unknown providers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/agent_runtime_provider_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps providers to configured binary paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
