# Claude Full prompt category

> Pure Simple coverage for agent query-source classification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full prompt category

Pure Simple coverage for agent query-source classification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/prompt_category_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for agent query-source classification.

## Scenarios

### Claude full prompt category

#### classifies named built-in agents

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classifies named built-in agents
- Check built-in agent names
   - Expected: getQuerySourceForAgent(Some("researcher"), true) equals `agent:builtin:researcher`
   - Expected: getQuerySourceForAgent(Some("planner"), true) equals `agent:builtin:planner`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies named built-in agents")
step("Check built-in agent names")
expect(getQuerySourceForAgent(Some("researcher"), true)).to_equal("agent:builtin:researcher")
expect(getQuerySourceForAgent(Some("planner"), true)).to_equal("agent:builtin:planner")
```

</details>

#### uses default for unnamed built-in agents

- uses default for unnamed built-in agents
- Check built-in default
   - Expected: getQuerySourceForAgent(nil, true) equals `agent:default`
   - Expected: getQuerySourceForAgent(Some(""), true) equals `agent:default`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses default for unnamed built-in agents")
step("Check built-in default")
expect(getQuerySourceForAgent(nil, true)).to_equal("agent:default")
expect(getQuerySourceForAgent(Some(""), true)).to_equal("agent:default")
```

</details>

#### classifies custom agents regardless of name

- classifies custom agents regardless of name
- Check custom agents
   - Expected: getQuerySourceForAgent(nil, false) equals `agent:custom`
   - Expected: getQuerySourceForAgent(Some("researcher"), false) equals `agent:custom`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies custom agents regardless of name")
step("Check custom agents")
expect(getQuerySourceForAgent(nil, false)).to_equal("agent:custom")
expect(getQuerySourceForAgent(Some("researcher"), false)).to_equal("agent:custom")
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

- Canonical SPipe generation for source `7bc978b839e5991f6f4ad3c80ca9db3e306931fca4014cbd6e06f5f1c2406f59`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7bc978b839e5991f6f4ad3c80ca9db3e306931fca4014cbd6e06f5f1c2406f59`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7bc978b839e5991f6f4ad3c80ca9db3e306931fca4014cbd6e06f5f1c2406f59`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/prompt_category_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/prompt_category_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/prompt_category_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/prompt_category_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/prompt_category_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies named built-in agents' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/prompt_category_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses default for unnamed built-in agents' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/prompt_category_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies custom agents regardless of name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
