# Claude Full CLI Agents Handler

> Checks agents subcommand formatting and grouping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CLI Agents Handler

Checks agents subcommand formatting and grouping.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/handlers/agents_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks agents subcommand formatting and grouping.

## Scenarios

### Claude full cli agents handler

#### formats an agent with model and memory

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- formats an agent with model and memory
- Agent type is always first, optional model and memory follow
   - Expected: formatAgent(ResolvedAgent.new("alpha", "general", "project", "", "")) equals `general`
   - Expected: formatAgent(ResolvedAgent.new("alpha", "general", "project", "sonnet", "")) equals `general · sonnet`
   - Expected: formatAgent(ResolvedAgent.new("alpha", "general", "project", "sonnet", "2MB")) equals `general · sonnet · 2MB memory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats an agent with model and memory")
step("Agent type is always first, optional model and memory follow")
expect(formatAgent(ResolvedAgent.new("alpha", "general", "project", "", ""))).to_equal("general")
expect(formatAgent(ResolvedAgent.new("alpha", "general", "project", "sonnet", ""))).to_equal("general · sonnet")
expect(formatAgent(ResolvedAgent.new("alpha", "general", "project", "sonnet", "2MB"))).to_equal("general · sonnet · 2MB memory")
```

</details>

#### prints no agents message for empty output

- prints no agents message for empty output
- No groups means no configured agents
   - Expected: agentsHandlerOutput([]) equals `noAgentsMessage()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prints no agents message for empty output")
step("No groups means no configured agents")
expect(agentsHandlerOutput([])).to_equal(noAgentsMessage())
```

</details>

#### renders agents in source order

- renders agents in source order
- The Simple parity slice keeps source order to avoid slow class-array sort
   - Expected: filterAgentsBySource(agents, "project").len() equals `3`
   - Expected: sortAgentsByName(agents).len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders agents in source order")
step("The Simple parity slice keeps source order to avoid slow class-array sort")
val agents = [
    ResolvedAgent.new("zeta", "z", "project", "", ""),
    ResolvedAgent.new("alpha", "a", "project", "haiku", ""),
    ResolvedAgent.new("user", "u", "user", "", "1MB")
]
val output = agentsHandlerOutput(agents)
expect(output).to_contain(activeAgentsHeader(3))
expect(output).to_contain("  a · haiku")
expect(output).to_contain("  z")
expect(output).to_contain("  u · 1MB memory")
expect(filterAgentsBySource(agents, "project").len()).to_equal(3)
expect(sortAgentsByName(agents).len()).to_equal(3)
```

</details>

#### marks shadowed agents and excludes them from active count

- marks shadowed agents and excludes them from active count
- Shadowed entries show the winning source and do not increment active total
   - Expected: activeAgentCount([shadowed, live]) equals `1`
   - Expected: getOverrideSourceLabel("builtin") equals `Built-in`
   - Expected: shadowedPrefix("project") equals `(shadowed by Project)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("marks shadowed agents and excludes them from active count")
step("Shadowed entries show the winning source and do not increment active total")
val shadowed = ResolvedAgent.new("alpha", "a", "user", "", "").shadowedBy("project")
val live = ResolvedAgent.new("beta", "b", "user", "", "")
val output = agentsHandlerOutput([shadowed, live])
expect(activeAgentCount([shadowed, live])).to_equal(1)
expect(output).to_contain("1 active agents")
expect(output).to_contain("  (shadowed by Project) a")
expect(output).to_contain("  b")
expect(getOverrideSourceLabel("builtin")).to_equal("Built-in")
expect(shadowedPrefix("project")).to_equal("(shadowed by Project)")
```

</details>

#### exports source-backed dependency names

- exports source-backed dependency names
- Pin dynamic handler collaborators
   - Expected: agentSourceGroups().len() equals `3`
   - Expected: modelDisplaySource() equals `resolveAgentModelDisplay`
   - Expected: overrideResolverSource() equals `resolveAgentOverrides`
   - Expected: activeAgentFilterSource() equals `getActiveAgentsFromList`
   - Expected: definitionsLoaderSource() equals `getAgentDefinitionsWithOverrides`
   - Expected: cwdSource() equals `getCwd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed dependency names")
step("Pin dynamic handler collaborators")
expect(agentSourceGroups().len()).to_equal(3)
expect(modelDisplaySource()).to_equal("resolveAgentModelDisplay")
expect(overrideResolverSource()).to_equal("resolveAgentOverrides")
expect(activeAgentFilterSource()).to_equal("getActiveAgentsFromList")
expect(definitionsLoaderSource()).to_equal("getAgentDefinitionsWithOverrides")
expect(cwdSource()).to_equal("getCwd")
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9ecfe70c5bf09824bf609509f359a1be4541ff081f3ae874549d3cd1267504f9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9ecfe70c5bf09824bf609509f359a1be4541ff081f3ae874549d3cd1267504f9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9ecfe70c5bf09824bf609509f359a1be4541ff081f3ae874549d3cd1267504f9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/cli/handlers/agents_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/cli/handlers/agents_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/cli/handlers/agents_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/cli/handlers/agents_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/cli/handlers/agents_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/cli/handlers/agents_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats an agent with model and memory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/handlers/agents_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints no agents message for empty output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/handlers/agents_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders agents in source order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
