# Simple 2D RenderDoc Manual and Contract Audit

> Keeps executable modern SSpec, generated manuals, guides, cooperative review,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple 2D RenderDoc Manual and Contract Audit

Keeps executable modern SSpec, generated manuals, guides, cooperative review,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Keeps executable modern SSpec, generated manuals, guides, cooperative review,
and source-layout contracts synchronized.

## Scenarios

### Simple 2D RenderDoc documentation contract

#### mirrors every executable scenario into an operator manual

- mirrors every executable scenario into an operator manual
   - Exec capture: after_step
- Inspect all backend-equivalence spec and manual pairs
   - Expected: SPECS.len() equals `MANUALS.len()`
   - Expected: SPECS.len() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mirrors every executable scenario into an operator manual")
step("Inspect all backend-equivalence spec and manual pairs")
expect(SPECS.len()).to_equal(MANUALS.len())
expect(SPECS.len()).to_equal(13)  # oracle: the renderdoc matrix is exactly these 13 spec/manual pairs
var index = 0
while index < SPECS.len():
    expect(file_exists(SPECS[index])).to_be(true)
    expect(file_exists(MANUALS[index])).to_be(true)
    expect(file_read(MANUALS[index]).len()).to_be_greater_than(0)
    val legacy = MANUALS[index].replace("doc/06_spec/", "doc/06_spec/test/")
    expect(file_exists(legacy)).to_be(true)
    expect(file_read(legacy).len()).to_be_greater_than(0)
    index = index + 1
```

</details>

#### keeps modern steps requirements direct matchers and no fail placeholders

- keeps modern steps requirements direct matchers and no fail placeholders
   - Exec capture: after_step
- Audit scenario source quality
   - Expected: spec_text contains `"expect(true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps modern steps requirements direct matchers and no fail placeholders")
step("Audit scenario source quality")
for path in SPECS:
    val spec_text = file_read(path)
    expect(spec_text).to_contain("# @req")
    expect(spec_text).to_contain("step(")
    expect(spec_text).to_contain("expect(")
    if path != "test/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.spl":
        expect(spec_text.contains("pass_todo")).to_be(false)
        expect(spec_text.contains("expect(true).to_equal(true)")).to_be(false)
        expect(spec_text.contains("pending_")).to_be(false)
```

</details>

<details>
<summary>Advanced: rejects executable specs under the generated manual tree</summary>

#### rejects executable specs under the generated manual tree

- rejects executable specs under the generated manual tree
   - Exec capture: after_step
- Scan doc/06_spec for executable Simple files
   - Expected: code equals `0`
   - Expected: out equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects executable specs under the generated manual tree")
step("Scan doc/06_spec for executable Simple files")
val (out, _err, code) = process_run(
    "/bin/sh", ["-c", "find doc/06_spec -name '*_spec.spl' -print"])
expect(code).to_equal(0)  # oracle: find over doc/06_spec succeeds
expect(out).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: requires sidecar merge and highest-capability review ownership</summary>

#### requires sidecar merge and highest-capability review ownership

- requires sidecar merge and highest-capability review ownership
   - Exec capture: after_step
- Inspect cooperative review completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires sidecar merge and highest-capability review ownership")
step("Inspect cooperative review completion")
val plan = file_read(
    "doc/03_plan/agent_tasks/simple_2d_renderdoc_backend_equivalence.md")
expect(plan).to_contain("Merge owner: primary Codex `/root`")
expect(plan).to_contain("Final reviewer: highest available normal Codex")
expect(plan).to_contain("Generated-manual review owner: primary Codex")
expect(plan).to_contain("Sidecars were read-only design auditors")
```

</details>


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

- Canonical SPipe generation for source `81e257d61e469a8bec99c61525ce0a99698d0c410ee0469cfc78a6378cd6bdd2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `81e257d61e469a8bec99c61525ce0a99698d0c410ee0469cfc78a6378cd6bdd2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `81e257d61e469a8bec99c61525ce0a99698d0c410ee0469cfc78a6378cd6bdd2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.spl
mirror: doc/06_spec/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/simple_2d_renderdoc_manual_and_contract_audit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
