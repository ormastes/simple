# LLM Caret Embedded Tmux TUI

> Proves LLM Caret can render an embedded tmux-style TUI for separate agent processes with visible CPU and memory usage columns. The implementation reuses the existing `common.tmux_session_model` pane model and accepts process usage snapshots supplied by the caller.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Embedded Tmux TUI

Proves LLM Caret can render an embedded tmux-style TUI for separate agent processes with visible CPU and memory usage columns. The implementation reuses the existing `common.tmux_session_model` pane model and accepts process usage snapshots supplied by the caller.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/llm_caret_embedded_tmux.md |
| Plan | doc/03_plan/sys_test/llm_caret_embedded_tmux.md |
| Design | doc/05_design/app/llm_caret_embedded_tmux.md |
| Research | doc/01_research/local/llm_caret_embedded_tmux.md |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Proves LLM Caret can render an embedded tmux-style TUI for separate agent
processes with visible CPU and memory usage columns. The implementation reuses
the existing `common.tmux_session_model` pane model and accepts process usage
snapshots supplied by the caller.

**Requirements:** doc/02_requirements/feature/llm_caret_embedded_tmux.md
**Plan:** doc/03_plan/sys_test/llm_caret_embedded_tmux.md
**Design:** doc/05_design/app/llm_caret_embedded_tmux.md
**Research:** doc/01_research/local/llm_caret_embedded_tmux.md
**TUI Captures:** inline text returned by `render_agent_tmux_tui`

## Syntax

1. Launch or model an `AgentTeamProcess`.
2. Provide one `AgentProcessUsage` per process with CPU percent and memory MB.
3. Call `build_agent_tmux_embed` to create the tmux-like pane session.
4. Call `render_agent_tmux_tui` to display panes, process ids, status, CPU, and
   memory.

## Example

```text
LLM Caret Embedded Tmux
Team: team-1
Session: team-1
Pane Process CPU Memory
pane[0] spark pid=101 status=running cpu=12.5% mem=256MB
pane[1] haiku pid=102 status=running cpu=4.0% mem=128MB
```

## Pass Criteria

- Each modeled process has a separate pane row.
- The rendered TUI includes process id and status.
- The rendered TUI includes CPU percent.
- The rendered TUI includes memory MB.
- No scenario starts a real external process or host tmux.

## Traceability

| Requirement | Scenario | Evidence |
|---|---|---|
| REQ-001 | render separate agent processes with CPU and memory usage | imports and uses `build_agent_tmux_embed`, which wraps `common.tmux_session_model` |
| REQ-002 | render separate agent processes with CPU and memory usage | rendered text contains `pane[0] spark` and `pane[1] haiku` |
| REQ-003 | render separate agent processes with CPU and memory usage | rendered text contains `pid=101`, `cpu=12.5%`, and `mem=256MB` |
| REQ-004 | render separate agent processes with CPU and memory usage | usage values come from `AgentProcessUsage` fixture data |
| REQ-005 | both scenarios | executable assertions prove multi-process and empty-team output |
| NFR-003 | render an empty team as an idle pane | rendered text contains `pane[0] idle` and `mem=0MB` |

## Operator Flow

The operator-facing flow is intentionally small:

1. LLM Caret starts or models a team process.
2. A caller samples CPU and memory through an owner facade such as the existing
   process-monitor modules.
3. LLM Caret passes those snapshots to `build_agent_tmux_embed`.
4. The TUI renders a pane table that keeps process separation visible.
5. If a process has no usage sample yet, the row still renders with zero CPU and
   memory rather than hiding the process.

## Exclusions

This is not a host tmux integration test. It does not spawn tmux, attach a PTY,
poll `/proc`, sample CPU, or send keyboard input. Those behaviors belong to
smux/terminal/process-monitor owner lanes. This test only proves that LLM Caret
can embed and render the tmux-style process view using existing Simple-side
models.

## Failure Signals

- Only one pane row appears for a multi-process team.
- PID or status text disappears from a pane row.
- CPU percent is omitted or replaced by a nonnumeric placeholder.
- Memory MB is omitted or hidden behind a process-monitor implementation detail.
- Empty teams fail instead of rendering the explicit idle pane.
- A future change adds direct runtime, `/proc`, shell, or host tmux calls to the
  LLM Caret embedding module.

## Maintenance Notes

Keep this layer boring. If live process sampling is required, add or reuse an
owner facade in the process-monitor family and pass the sampled values into
`AgentProcessUsage`. If live terminal I/O is required, extend the smux or
terminal panel owner lane and keep LLM Caret as a consumer of a stable
session/pane API. Do not duplicate tmux state, keymaps, PTY handling, or process
sampling in `agent_tmux.spl`.

The generated TUI is intentionally plain text so SPipe manuals can embed it and
operators can inspect it in logs. A later full-screen interface can preserve the
same row labels while adding navigation.

## Runner Note

The verification target for this slice is the SSpec assertion count and summary:
two scenarios, zero assertion failures. The test does not require native process
launch, host tmux, or a live PTY.

## Evidence

Display policy: `embed_tui`

| Category | Count |
|----------|------:|
| TUI Captures | 1 |

### TUI Captures

| Item | Kind | Path |
|------|------|------|
| `inline text returned by `render_agent_tmux_tui`` | TUI capture | `inline text returned by `render_agent_tmux_tui`` |

## Scenarios

### LLM Caret embedded tmux TUI

#### should render separate agent processes with CPU and memory usage

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should render separate agent processes with CPU and memory usage
- Build a modeled team process
- Render the embedded tmux TUI


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should render separate agent processes with CPU and memory usage")
step("Build a modeled team process")
val spark = AgentProcess(agent_id: "spark", status: "running", reason: "process_running", pid: 101)
val haiku = AgentProcess(agent_id: "haiku", status: "running", reason: "process_running", pid: 102)
val team = AgentTeamProcess(team_id: "team-1", status: "started", reason: "started:2/2", processes: [spark, haiku])
val usages = [
    AgentProcessUsage(agent_id: "spark", pid: 101, cpu_percent: 12.5, memory_mb: 256),
    AgentProcessUsage(agent_id: "haiku", pid: 102, cpu_percent: 4.0, memory_mb: 128)
]
step("Render the embedded tmux TUI")
val embed = build_agent_tmux_embed(team, usages)
val tui = render_agent_tmux_tui(embed, team)
expect(tui).to_contain("LLM Caret Embedded Tmux")
expect(tui).to_contain("pane[0] spark")
expect(tui).to_contain("pane[1] haiku")
expect(tui).to_contain("pid=101")
expect(tui).to_contain("cpu=12.5%")
expect(tui).to_contain("mem=256MB")
```

</details>

#### should render an empty team as an idle pane

- should render an empty team as an idle pane
- Build an empty team process
- Render the idle embedded tmux TUI


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should render an empty team as an idle pane")
step("Build an empty team process")
val team = AgentTeamProcess(team_id: "empty-team", status: "empty", reason: "started:0/0", processes: [])
val embed = build_agent_tmux_embed(team, [])
step("Render the idle embedded tmux TUI")
val tui = render_agent_tmux_tui(embed, team)
expect(tui).to_contain("Session: empty-team")
expect(tui).to_contain("pane[0] idle")
expect(tui).to_contain("mem=0MB")
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


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/llm_caret_embedded_tmux.md`
- **Plan:** `doc/03_plan/sys_test/llm_caret_embedded_tmux.md`
- **Design:** `doc/05_design/app/llm_caret_embedded_tmux.md`
- **Research:** `doc/01_research/local/llm_caret_embedded_tmux.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f5bc9adf6e9399c040f004ee1a0849246c19106e9cd067a8e68fcc424d3307f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f5bc9adf6e9399c040f004ee1a0849246c19106e9cd067a8e68fcc424d3307f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f5bc9adf6e9399c040f004ee1a0849246c19106e9cd067a8e68fcc424d3307f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.spl:122:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render separate agent processes with CPU and memory usage' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should render separate agent processes with CPU and memory usage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.spl:143:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render an empty team as an idle pane' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should render an empty team as an idle pane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
