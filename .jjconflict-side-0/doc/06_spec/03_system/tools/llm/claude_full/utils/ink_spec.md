# Claude Full ink utils

> Pure Simple coverage for agent color to Ink color mapping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full ink utils

Pure Simple coverage for agent color to Ink color mapping.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/ink_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for agent color to Ink color mapping.

## Scenarios

### Claude full ink utils

#### defaults missing color to subagent cyan

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults missing color to subagent cyan
- Check default color
   - Expected: toInkColor(nil) equals `cyan_FOR_SUBAGENTS_ONLY`
   - Expected: toInkColor(Some("")) equals `cyan_FOR_SUBAGENTS_ONLY`
   - Expected: defaultAgentThemeColor() equals `cyan_FOR_SUBAGENTS_ONLY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defaults missing color to subagent cyan")
step("Check default color")
expect(toInkColor(nil)).to_equal("cyan_FOR_SUBAGENTS_ONLY")
expect(toInkColor(Some(""))).to_equal("cyan_FOR_SUBAGENTS_ONLY")
expect(defaultAgentThemeColor()).to_equal("cyan_FOR_SUBAGENTS_ONLY")
```

</details>

#### maps known agent colors to theme colors

- maps known agent colors to theme colors
- Check theme mapping
   - Expected: toInkColor(Some("blue")) equals `blue_FOR_SUBAGENTS_ONLY`
   - Expected: toInkColor(Some("cyan")) equals `cyan_FOR_SUBAGENTS_ONLY`
   - Expected: agentColorToThemeColor("red") equals `Some("red_FOR_SUBAGENTS_ONLY")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps known agent colors to theme colors")
step("Check theme mapping")
expect(toInkColor(Some("blue"))).to_equal("blue_FOR_SUBAGENTS_ONLY")
expect(toInkColor(Some("cyan"))).to_equal("cyan_FOR_SUBAGENTS_ONLY")
expect(agentColorToThemeColor("red")).to_equal(Some("red_FOR_SUBAGENTS_ONLY"))
```

</details>

#### falls back to raw ansi colors for unknown names

- falls back to raw ansi colors for unknown names
- Check ansi fallback
   - Expected: toInkColor(Some("gray")) equals `ansi:gray`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("falls back to raw ansi colors for unknown names")
step("Check ansi fallback")
expect(toInkColor(Some("gray"))).to_equal("ansi:gray")
expect(agentColorToThemeColor("gray")).to_be_nil()
```

</details>

#### covers the upstream agent color table

- covers the upstream agent color table
- Check all mapped colors
   - Expected: agentColorToThemeColor("red") equals `Some("red_FOR_SUBAGENTS_ONLY")`
   - Expected: agentColorToThemeColor("green") equals `Some("green_FOR_SUBAGENTS_ONLY")`
   - Expected: agentColorToThemeColor("yellow") equals `Some("yellow_FOR_SUBAGENTS_ONLY")`
   - Expected: agentColorToThemeColor("purple") equals `Some("purple_FOR_SUBAGENTS_ONLY")`
   - Expected: agentColorToThemeColor("orange") equals `Some("orange_FOR_SUBAGENTS_ONLY")`
   - Expected: agentColorToThemeColor("pink") equals `Some("pink_FOR_SUBAGENTS_ONLY")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("covers the upstream agent color table")
step("Check all mapped colors")
expect(agentColorToThemeColor("red")).to_equal(Some("red_FOR_SUBAGENTS_ONLY"))
expect(agentColorToThemeColor("green")).to_equal(Some("green_FOR_SUBAGENTS_ONLY"))
expect(agentColorToThemeColor("yellow")).to_equal(Some("yellow_FOR_SUBAGENTS_ONLY"))
expect(agentColorToThemeColor("purple")).to_equal(Some("purple_FOR_SUBAGENTS_ONLY"))
expect(agentColorToThemeColor("orange")).to_equal(Some("orange_FOR_SUBAGENTS_ONLY"))
expect(agentColorToThemeColor("pink")).to_equal(Some("pink_FOR_SUBAGENTS_ONLY"))
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

- Canonical SPipe generation for source `990427948323d8f853c9dfa1c2bcd14dbd9fe1cd9302198fc7494921133a3118`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `990427948323d8f853c9dfa1c2bcd14dbd9fe1cd9302198fc7494921133a3118`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `990427948323d8f853c9dfa1c2bcd14dbd9fe1cd9302198fc7494921133a3118`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/ink_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/ink_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/ink_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/ink_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/ink_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults missing color to subagent cyan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/ink_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps known agent colors to theme colors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/ink_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back to raw ansi colors for unknown names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
