# Claude Full ConfirmStep Component

> Exercises the owned wizard-confirm gate behaviorally through the importable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full ConfirmStep Component

Exercises the owned wizard-confirm gate behaviorally through the importable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the owned wizard-confirm gate behaviorally through the importable
ConfirmStep wrapper. As a wizard user I see a confirmation gate that only
enables when the draft is complete, so an incomplete draft can never be
submitted. The modeled TypeScript source parity floor is asserted through the
wrapper's own source-lines helper.

## Scenarios

### Claude full ConfirmStep component

#### gates confirmation on draft completeness

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- gates confirmation on draft completeness
- Check the confirm gate title
   - Expected: confirmStepWrapperTitle() equals `Confirm agent`
- An incomplete draft is not ready to create
- A complete draft is ready to create
   - Expected: confirmStepWrapperStatus(true) equals `Ready to create`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gates confirmation on draft completeness")
step("Check the confirm gate title")
expect(confirmStepWrapperTitle()).to_equal("Confirm agent")

step("An incomplete draft is not ready to create")
expect(confirmStepWrapperStatus(false)).to_contain("Missing required fields")

step("A complete draft is ready to create")
expect(confirmStepWrapperStatus(true)).to_equal("Ready to create")
```

</details>

#### keeps the modeled source parity floor

- keeps the modeled source parity floor
- Assert the wrapper reports its modeled source floor
   - Expected: confirmStepWrapperSourceLinesModeled() equals `73`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the modeled source parity floor")
step("Assert the wrapper reports its modeled source floor")
expect(confirmStepWrapperSourceLinesModeled()).to_be_greater_than(0)
expect(confirmStepWrapperSourceLinesModeled()).to_equal(73)
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

- Canonical SPipe generation for source `464758bc2bd190a45cfe68cd3ab0a159c874709b7e51570449cc857ea2e296f6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `464758bc2bd190a45cfe68cd3ab0a159c874709b7e51570449cc857ea2e296f6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `464758bc2bd190a45cfe68cd3ab0a159c874709b7e51570449cc857ea2e296f6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gates confirmation on draft completeness' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/agent_confirm_step_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the modeled source parity floor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
