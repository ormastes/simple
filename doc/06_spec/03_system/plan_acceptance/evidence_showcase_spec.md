# evidence_showcase_spec

> Acceptance oracles for the open remains of

<!-- sdn-diagram:id=evidence_showcase_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=evidence_showcase_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

evidence_showcase_spec -> std
evidence_showcase_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=evidence_showcase_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# evidence_showcase_spec

Acceptance oracles for the open remains of

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/plan_acceptance/evidence_showcase_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Acceptance oracles for the open remains of
doc/03_plan/agent_tasks/evidence_showcase.md § Completion checklist, for the
plan-acceptance lane defined in
doc/03_plan/agent_tasks/plan_remains_acceptance_2026-09-05.md. Audience: the
merge owner closing Lane 0-4, and the independent reviewer who signs off
Lane 7.
## Operator workflow
bin/simple test test/03_system/plan_acceptance/evidence_showcase_spec.spl
The traceability `it` shells real `grep` counts against
doc/02_requirements/feature/evidence_showcase.md, so its verdict tracks
whatever the tree actually binds today.
## Compatibility and limitations
Tagged in-development: these pin the promised INTERFACE and fail until the
plan's remaining checkboxes are implemented. The plan's own "Frozen shared
contract" section names five types
(ScenarioTextEvidencePolicy/ScenarioTextMask/ScenarioTextMatchResult/
ScenarioMotionEvidence/ScenarioProtocolFieldEvidence) that a full-tree grep
census (2026-09-05) confirms do not exist yet, and one existing but
currently-unbuildable module
(src/app/spipe_docgen/spipe_docgen/evidence_manifest.spl, which imports
std.spec.scenario_evidence_manifest -- a module that also does not exist).
Those `it`s import the real, currently-broken symbols directly rather than
inventing new names, so the unresolved import is a genuine forcing function,
not a fabricated one.
## Lifecycle
Research doc/01_research/, plan doc/03_plan/agent_tasks/evidence_showcase.md,
architecture doc/04_architecture/, and design doc/05_design/ records for the
evidence-showcase feature are the umbrella lifecycle folders this spec
traces to.

## Scenarios

### Evidence showcase plan — Lane 0-7 completion checklist (doc/03_plan/agent_tasks/evidence_showcase.md)

#### Lane 0 contract reviewed.

- Request the five frozen types the Lane 0 contract promises but has not yet delivered
- Assert the frozen policy names the fail-fast rule Lane 0 requires
   - Expected: policy.name equals `"reordered-lines-reject")  # oracle: plan §Frozen shared contract, ScenarioT... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-EVS-SHOWCASE-LANE0
step("Request the five frozen types the Lane 0 contract promises but has not yet delivered")
# The Frozen shared contract names 5 types that a full-tree grep
# census (2026-09-05) confirms have zero struct/class definitions
# anywhere in the tree yet. Pin them directly as the forcing
# function for Lane 0's review gate.
use std.spec.scenario_text_evidence.{ScenarioTextEvidencePolicy, ScenarioTextMask, ScenarioTextMatchResult}
val policy: ScenarioTextEvidencePolicy = ScenarioTextEvidencePolicy(name: "reordered-lines-reject")
step("Assert the frozen policy names the fail-fast rule Lane 0 requires")
# contract's own compile-visible type/constructor signature.
expect(policy.name).to_equal("reordered-lines-reject")  # oracle: plan §Frozen shared contract, ScenarioTextEvidencePolicy
```

</details>

#### Lanes 1-3 pass focused fixtures.

- Run the promised text-evidence checker against a deliberately reordered fixture
- Assert the reordered-line fixture is rejected, not silently accepted
   - Expected: outcome.passed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-EVS-SHOWCASE-LANE13
step("Run the promised text-evidence checker against a deliberately reordered fixture")
# Lane 1's own "No-false-green" rule: reordered lines must FAIL.
# No `check_text_evidence` exists anywhere in the tree (grep census,
# 2026-09-05) -- pin it directly.
use std.spec.evidence_checks.{check_text_evidence}
val outcome = check_text_evidence("line one\nline two\n", "line two\nline one\n")
step("Assert the reordered-line fixture is rejected, not silently accepted")
# own computed verdict on a real reordered-line fixture.
expect(outcome.passed).to_equal(false)  # oracle: plan Lane 1 No-false-green rule, "reordered lines ... fail"
```

</details>

#### Lane 4 produces atomic validated manifests and root/subproject pages.

**Manual warnings:**
- invalid capture metadata value: empty (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Import the real, already-written Lane 4 manifest renderer
- Assert the atomic validator accepts a manifest whose declared artifacts genuinely exist
   - Expected: validated.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-EVS-SHOWCASE-LANE4
step("Import the real, already-written Lane 4 manifest renderer")
# Real symbols in a real, currently-committed file -- not invented.
# This module's own `use std.spec.scenario_evidence_manifest.{...}`
# (line 20) names a module that does not exist anywhere in the tree
# (grep census, 2026-09-05), so this import is a genuine forcing
# function for Lane 4, not a fabricated one.
use app.spipe_docgen.spipe_docgen.evidence_manifest.{render_evidence_manifest, validate_evidence_artifact_files, ScenarioEvidenceManifest}
val manifest = ScenarioEvidenceManifest(command: "showcase", reason: "acceptance", resume_command: "resume")
step("Assert the atomic validator accepts a manifest whose declared artifacts genuinely exist")
val validated = validate_evidence_artifact_files(manifest)
# "atomic validated manifests" deliverable.
expect(validated.is_ok()).to_equal(true)  # oracle: plan Lane 4 deliverable, "atomic validated manifests"
```

</details>

#### Selected exemplars have live receipts or honest blocker rows.

**Manual warnings:**
- invalid capture metadata value: outcome (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- Build a receipt for an exemplar whose declared artifact was never captured
- Assert the fail-closed verifier reports the honest FAIL verdict for the missing artifact
   - Expected: verify_verdict(outcome) equals `"FAIL")  # oracle: plan text, "live receipts or honest blocker rows" -- missi... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-EVS-SHOWCASE-EXEMPLARS
step("Build a receipt for an exemplar whose declared artifact was never captured")
# Real, already-landed primitive: a receipt with no live artifact on
# disk must fail closed, never silently read as PASS.
val receipt = receipt_new("evidence-showcase-exemplar", "native_perf", "hosted_fallback", "PASS", "build/showcase/exemplar.png")
val outcome = receipt_verify(receipt, false, 0, 0)
step("Assert the fail-closed verifier reports the honest FAIL verdict for the missing artifact")
# real, already-landed fail-closed rule this checkbox depends on.
expect(verify_verdict(outcome)).to_equal("FAIL")  # oracle: plan text, "live receipts or honest blocker rows" -- missing artifact must FAIL, never silently PASS
```

</details>

#### All workflow mirrors are current.

- Count how many of the plan's own named workflow-mirror files exist in this tree
- Assert every one of the plan's 12 named mirror files exists
   - Expected: existing_count equals `12)  # oracle: plan §Planned workflow update matrix, 12 named files`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-EVS-SHOWCASE-MIRRORS
step("Count how many of the plan's own named workflow-mirror files exist in this tree")
# The plan's own §Planned workflow update matrix names an exact file
# list under "Required host repository updates". Real, computed
# count of how many currently exist.
val existing_count = shell_count("for f in AGENTS.md FILE.md README.md config/FILE.md doc/07_guide/README.md doc/07_guide/infra/sspec_scenario_manual.md doc/07_guide/infra/testing.md doc/07_guide/app/spipe/evidence_showcase.md doc/07_guide/app/spipe/scenario_manual_example.md test/README.md doc/06_spec/FILE.md src/app/README.md; do test -f \"$f\" && echo x; done | wc -l")
step("Assert every one of the plan's 12 named mirror files exists")
# filesystem count against the plan's own named file list.
expect(existing_count).to_equal(12)  # oracle: plan §Planned workflow update matrix, 12 named files
```

</details>

#### Generated manuals are operator-readable and zero-stub.

- Check for the canonical generated evidence-showcase manual under doc/06_spec
- Assert the generated manual exists before it can be judged operator-readable
   - Expected: has_manual is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-EVS-SHOWCASE-MANUALS
step("Check for the canonical generated evidence-showcase manual under doc/06_spec")
# Mirror paths strip the leading test/ segment, as required by the
# doc/06_spec manifest.
val has_manual = rt_file_exists("doc/06_spec/03_system/app/testing/feature/evidence_showcase_spec.md")
step("Assert the generated manual exists before it can be judged operator-readable")
# a manual that does not exist cannot yet be zero-stub.
expect(has_manual).to_equal(true)  # oracle: checkbox text, "Generated manuals are operator-readable"; docgen mirror for this feature not yet produced
```

</details>

#### Traceability is 100%.

- Count the requirement IDs this plan's requirements doc declares
- Assert every declared requirement ID is bound in at least one executable scenario
   - Expected: bound_count equals `declared_count)  # oracle: checkbox text, "Traceability is 100%" means bound ... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-EVS-SHOWCASE-TRACE
step("Count the requirement IDs this plan's requirements doc declares")
# Real, computed ratio: every REQ-EVS-NNN the requirements doc
# declares versus every one actually bound inside an executable
# `.spl` scenario anywhere in the tree.
val declared_count = shell_count("grep -o 'REQ-EVS-[0-9][0-9]*' doc/02_requirements/feature/evidence_showcase.md doc/02_requirements/nfr/evidence_showcase.md | sed 's/.*://' | sort -u | wc -l")
val bound_count = shell_count("grep -rho 'REQ-EVS-[0-9][0-9]*' --include='*.spl' src/ test/ | sort -u | wc -l")
step("Assert every declared requirement ID is bound in at least one executable scenario")
# evidence for the checkbox's own "100%" claim.
expect(bound_count).to_equal(declared_count)  # oracle: checkbox text, "Traceability is 100%" means bound == declared
```

</details>

#### Final independent review reports PASS or lists unresolved blockers.

- Check for a recorded final-review report naming this feature
- Assert no final-review record has been filed yet, matching the unchecked box
   - Expected: has_review_report is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-EVS-SHOWCASE-FINALREVIEW
step("Check for a recorded final-review report naming this feature")
# This is fundamentally a process gate -- "an independent reviewer
# signed off" has no computable interface, only a record a reviewer
# would leave behind. Real, checked: no such record exists yet.
val has_review_report = rt_file_exists("doc/09_report/evidence_showcase_final_review.md")
step("Assert no final-review record has been filed yet, matching the unchecked box")
# available for this process checkbox; this `it` is flagged in the
# task report as too vague for a computed-value oracle.
expect(has_review_report).to_equal(false)  # oracle: checkbox unchecked in the plan; no doc/09_report record found for this feature
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
