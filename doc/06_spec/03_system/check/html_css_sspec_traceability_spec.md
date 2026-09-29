# HTML/CSS executable SSpec traceability gate

> Proves the traceability checker cannot promote inventory text or unbound execution counts to behavioral HTML/CSS evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML/CSS executable SSpec traceability gate

Proves the traceability checker cannot promote inventory text or unbound execution counts to behavioral HTML/CSS evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/05_design/simple_web_browser_engine_production_hardening.md |
| Research | doc/01_research/local/simple_web_browser_engine_production_hardening.md |
| Source | `test/03_system/check/html_css_sspec_traceability_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Proves the traceability checker cannot promote inventory text or unbound
execution counts to behavioral HTML/CSS evidence.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md
**Requirements:** doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md
**NFR:** doc/02_requirements/nfr/simple_web_browser_engine_production_hardening.md
**Design:** doc/05_design/simple_web_browser_engine_production_hardening.md
**Architecture:** doc/04_architecture/simple_web_browser_engine_production_hardening.md
**Research:** doc/01_research/local/simple_web_browser_engine_production_hardening.md
**Domain Research:** doc/01_research/domain/simple_web_browser_engine_production_hardening.md

## Claim boundary

This specification validates the evidence gate.

It does not claim complete HTML support.

It does not claim complete CSS support.

It does not claim that inventory occurrence is rendering.

It does not claim that a source-only scenario has executed.

It does not claim that a generated manual is current without a source binding.

It does not accept the deployed release wrapper as a qualified runner.

It does not accept a Rust seed as a pure-Simple target runtime.

It does not accept Stage 2 or Stage 3 compiler-only artifacts as test runners.

It does not fabricate runner admission or execution receipts.

Behavioral status remains `evidence-blocked`.

The current blocker is `trusted-runner-admission-unavailable`.

## Trust model

Inventory names are diagnostic inputs.

Executable SSpec scenarios are behavior definitions.

Scenario assertions are not execution receipts.

Generated manuals are review surfaces, not execution receipts.

Runner path text is not runner provenance.

An environment-provided SHA is not independent trust.

A current jj revision string is not proof that a runner was built from it.

A matrix hash proves integrity only after its producer is admitted.

Counts supplied by an evidence file are untrusted.

PASS requires an existing reviewed bootstrap or release admission contract.

No new PKI is introduced by this checker.

Until trusted admission exists, complete self-authored evidence fails closed.

## Evidence classes

`inventory` means a standardized name was discovered.

`assigned` means a canonical executable scenario names the row.

`semantic` means DOM or computed-style identity is asserted.

`layout` means stable geometry, parentage, order, or clipping is asserted.

`DrawIR` means canonical composition commands or styles are asserted.

`Engine2D` means exact discriminating pixels, counts, or checksums are asserted.

`negative` means fallback, invalid, unsupported, or baseline behavior is asserted.

`executed` means a qualified runner reported the exact scenario result.

`documented` means the canonical mirrored manual matches the executable source.

Only the complete applicable chain can support behavioral PASS.

## Frozen manual steps

- `Verify executable HTML and CSS traceability`

- `Trace HTML elements through Web semantics and Draw IR`

- `Trace implemented CSS properties through canonical rendering`

- `Classify unsupported CSS properties without false implementation claims`

The first step belongs to this aggregate truth gate.

The remaining steps belong to behavior specifications.

Frozen spelling prevents generated manuals from drifting into parallel vocabularies.

## Failure discrimination

`missing-behavior-evidence` means no provenance input exists.

`incomplete-behavior-evidence` means required provenance fields are absent.

`trusted-runner-admission-unavailable` means all self-authored fields remain untrusted.

`inventory-fetch-disabled` means offline inventory collection was requested.

`inventory-fetch-failed:*` means the standards inventory could not be refreshed.

Inventory failure and runner-admission failure remain separate evidence rows.

An empty executed count is not converted into a failed scenario count.

A failed behavioral gate is not converted into unsupported HTML or CSS.

A forged receipt never becomes PASS because its internal hashes agree.

## Examples

Example: no behavior evidence file exists.

Expected result: `evidence-blocked`, reason `missing-behavior-evidence`.

Example: an evidence file contains only passed and failed counts.

Expected result: `evidence-blocked`, reason `incomplete-behavior-evidence`.

Example: the canonical wrapper path, its actual SHA, the current jj revision,
and a matrix SHA are supplied by the caller.

Expected result: `evidence-blocked`, reason
`trusted-runner-admission-unavailable`.

Example: modern HTML and CSS system roots exist.

Expected result: they are discovered but do not become proof by occurrence.

Example: an old manual contains a scenario name.

Expected result: no behavioral PASS is inferred.

## Current evidence state

The behavior-first plan exists.

Modern HTML and CSS system-test roots exist.

The checker emits inventory and behavioral fields separately.

The checker reports zero executed scenarios without trusted admission.

The checker emits no receipt digest without trusted admission.

Canonical manuals still require qualified generation and review.

No target runtime was executed while authoring this contract.

No bootstrap was performed while authoring this contract.

No execution PASS is recorded by this manual.

## Acceptance

- Missing qualified execution evidence remains evidence-blocked.
- A claimed PASS without its runner, matrix, hashes, and current manuals fails.
- Inventory counts remain diagnostic and cannot become behavioral PASS.
- Complete caller-authored provenance around the canonical wrapper still fails.
- Executed, passed, failed, empty, and stub counts remain explicit.
- Receipt hashes remain empty until trusted execution can produce them.
- Standards inventory roots include modern HTML and CSS system specifications.
- The generated manual preserves this trust boundary and failure vocabulary.

## Scenarios

### HTML/CSS executable SSpec traceability

#### should remain evidence-blocked when no qualified execution receipt exists

- Verify executable HTML and CSS traceability
   - Expected: code equals `0`
- Reject inventory occurrence as behavioral evidence
   - Expected: _traceability_value(evidence, "html_css_sspec_traceability_status") equals `evidence-blocked`
   - Expected: _traceability_value(evidence, "html_css_sspec_traceability_reason") equals `missing-behavior-evidence`
   - Expected: _traceability_value(evidence, "html_css_sspec_traceability_behavior_evidence_valid") equals `false`
   - Expected: _traceability_value(evidence, "html_css_sspec_traceability_executed_count") equals `0`
   - Expected: _traceability_value(evidence, "html_css_sspec_traceability_failed_count") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify executable HTML and CSS traceability")
val command = "rm -rf build/test-html-css-sspec-missing && BUILD_DIR=build/test-html-css-sspec-missing REPORT_PATH=build/test-html-css-sspec-missing/report.md HTML_CSS_SSPEC_FETCH=0 HTML_CSS_SSPEC_BEHAVIOR_EVIDENCE=build/test-html-css-sspec-missing/missing.env sh scripts/check/check-html-css-sspec-traceability.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Reject inventory occurrence as behavioral evidence")
val evidence = file_read("build/test-html-css-sspec-missing/evidence.env") ?? ""
expect(_traceability_value(evidence, "html_css_sspec_traceability_status")).to_equal("evidence-blocked")
expect(_traceability_value(evidence, "html_css_sspec_traceability_reason")).to_equal("missing-behavior-evidence")
expect(_traceability_value(evidence, "html_css_sspec_traceability_behavior_evidence_valid")).to_equal("false")
expect(_traceability_value(evidence, "html_css_sspec_traceability_executed_count")).to_equal("0")
expect(_traceability_value(evidence, "html_css_sspec_traceability_failed_count")).to_equal("0")
```

</details>

#### should reject unbound PASS counts without current artifacts and runner provenance

- Write a forged counts-only PASS receipt
   - Expected: code equals `0`
- Require matrix, source, manual, runner, and receipt hashes
   - Expected: _traceability_value(evidence, "html_css_sspec_traceability_status") equals `evidence-blocked`
   - Expected: _traceability_value(evidence, "html_css_sspec_traceability_reason") equals `incomplete-behavior-evidence`
   - Expected: _traceability_value(evidence, "html_css_sspec_traceability_behavior_evidence_valid") equals `false`
   - Expected: _traceability_value(evidence, "html_css_sspec_traceability_runner_sha256") equals ``
   - Expected: _traceability_value(evidence, "html_css_sspec_traceability_matrix_sha256") equals ``
   - Expected: _traceability_value(evidence, "html_css_sspec_traceability_stub_count") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write a forged counts-only PASS receipt")
val command = "rm -rf build/test-html-css-sspec-forged && mkdir -p build/test-html-css-sspec-forged && printf '%s\\n' 'html_css_behavior_status=pass' 'html_css_behavior_executed_count=394' 'html_css_behavior_passed_count=394' 'html_css_behavior_failed_count=0' > build/test-html-css-sspec-forged/forged.env && BUILD_DIR=build/test-html-css-sspec-forged/out REPORT_PATH=build/test-html-css-sspec-forged/report.md HTML_CSS_SSPEC_FETCH=0 HTML_CSS_SSPEC_BEHAVIOR_EVIDENCE=build/test-html-css-sspec-forged/forged.env sh scripts/check/check-html-css-sspec-traceability.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Require matrix, source, manual, runner, and receipt hashes")
val evidence = file_read("build/test-html-css-sspec-forged/out/evidence.env") ?? ""
expect(_traceability_value(evidence, "html_css_sspec_traceability_status")).to_equal("evidence-blocked")
expect(_traceability_value(evidence, "html_css_sspec_traceability_reason")).to_equal("incomplete-behavior-evidence")
expect(_traceability_value(evidence, "html_css_sspec_traceability_behavior_evidence_valid")).to_equal("false")
expect(_traceability_value(evidence, "html_css_sspec_traceability_runner_sha256")).to_equal("")
expect(_traceability_value(evidence, "html_css_sspec_traceability_matrix_sha256")).to_equal("")
expect(_traceability_value(evidence, "html_css_sspec_traceability_stub_count")).to_equal("")
```

</details>

#### should reject complete forged provenance around the canonical executable path

- Write every accepted provenance input around the canonical release wrapper
   - Expected: code equals `0`
- Reject complete self-authored evidence without trusted release admission
   - Expected: _traceability_value(evidence, "html_css_sspec_traceability_status") equals `evidence-blocked`
   - Expected: _traceability_value(evidence, "html_css_sspec_traceability_reason") equals `trusted-runner-admission-unavailable`
   - Expected: _traceability_value(evidence, "html_css_sspec_traceability_behavior_evidence_valid") equals `false`
   - Expected: _traceability_value(evidence, "html_css_sspec_traceability_executed_count") equals `0`
   - Expected: _traceability_value(evidence, "html_css_sspec_traceability_receipt_sha256") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write every accepted provenance input around the canonical release wrapper")
val command = "rm -rf build/test-html-css-sspec-complete-forgery && mkdir -p build/test-html-css-sspec-complete-forgery && printf '%s\\n' 'kind\\tname\\treq\\tsupport\\tspec\\tscenario\\tmanual\\tsource_sha256\\tsemantic_oracle\\tlayout_draw_ir_oracle\\tengine2d_oracle\\tnegative_control' > build/test-html-css-sspec-complete-forgery/matrix.tsv && runner_sha=$(sha256sum bin/release/simple | cut -d' ' -f1) && matrix_sha=$(sha256sum build/test-html-css-sspec-complete-forgery/matrix.tsv | cut -d' ' -f1) && revision=$(jj log --no-graph -r @ -T commit_id) && printf '%s\\n' 'html_css_behavior_runner_path=bin/release/simple' \"html_css_behavior_runner_sha256=$runner_sha\" \"html_css_behavior_source_revision=$revision\" 'html_css_behavior_matrix_path=build/test-html-css-sspec-complete-forgery/matrix.tsv' \"html_css_behavior_matrix_sha256=$matrix_sha\" > build/test-html-css-sspec-complete-forgery/forged.env && BUILD_DIR=build/test-html-css-sspec-complete-forgery/out REPORT_PATH=build/test-html-css-sspec-complete-forgery/report.md HTML_CSS_SSPEC_FETCH=0 HTML_CSS_SSPEC_BEHAVIOR_EVIDENCE=build/test-html-css-sspec-complete-forgery/forged.env sh scripts/check/check-html-css-sspec-traceability.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Reject complete self-authored evidence without trusted release admission")
val evidence = file_read("build/test-html-css-sspec-complete-forgery/out/evidence.env") ?? ""
expect(_traceability_value(evidence, "html_css_sspec_traceability_status")).to_equal("evidence-blocked")
expect(_traceability_value(evidence, "html_css_sspec_traceability_reason")).to_equal("trusted-runner-admission-unavailable")
expect(_traceability_value(evidence, "html_css_sspec_traceability_behavior_evidence_valid")).to_equal("false")
expect(_traceability_value(evidence, "html_css_sspec_traceability_executed_count")).to_equal("0")
expect(_traceability_value(evidence, "html_css_sspec_traceability_receipt_sha256")).to_equal("")
```

</details>

#### should expose modern HTML and CSS system roots without treating them as proof

- Verify executable HTML and CSS traceability
- Keep behavior proof separate from inventory discovery


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify executable HTML and CSS traceability")
val source = file_read("scripts/check/check-html-css-sspec-traceability.shs") ?? ""
expect(source).to_contain("test/03_system/feature/web_platform/html")
expect(source).to_contain("test/03_system/feature/web_platform/css")

step("Keep behavior proof separate from inventory discovery")
expect(source).to_contain("HTML_CSS_SSPEC_BEHAVIOR_EVIDENCE")
expect(source).to_contain("missing-behavior-evidence")
expect(source).to_contain("incomplete-behavior-evidence")
expect(source).to_contain("matrix_sha256")
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


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/html_css_spec_traceability.md`
- **Design:** `doc/05_design/simple_web_browser_engine_production_hardening.md`
- **Research:** `doc/01_research/local/simple_web_browser_engine_production_hardening.md`


</details>
