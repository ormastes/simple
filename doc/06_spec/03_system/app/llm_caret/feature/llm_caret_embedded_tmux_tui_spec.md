# LLM Caret Embedded Tmux TUI

> Verifies the llm caret embedded tmux tui behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Embedded Tmux TUI

Verifies the llm caret embedded tmux tui behaviour end to end so maintainers of this

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
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the llm caret embedded tmux tui behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

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

- Verify: should render separate agent processes with CPU and memory usage
- Build a modeled team process
- Render the embedded tmux TUI


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005
step("Verify: should render separate agent processes with CPU and memory usage")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should render an empty team as an idle pane
- Build an empty team process
- Render the idle embedded tmux TUI


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005
step("Verify: should render an empty team as an idle pane")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a8087862959d6d714d7a335966eb1b2b2aad673e6c1240f14b1417279a35f49b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a8087862959d6d714d7a335966eb1b2b2aad673e6c1240f14b1417279a35f49b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a8087862959d6d714d7a335966eb1b2b2aad673e6c1240f14b1417279a35f49b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.spl:132:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render separate agent processes with CPU and memory usage' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.spl:154:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render an empty team as an idle pane' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
