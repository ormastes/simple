# Tooling Artifact Collector Specification

> Tests covering LLM dashboard tooling artifact collector.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tooling Artifact Collector Specification

## Scenarios

### LLM dashboard tooling artifact collector

#### summarizes context and ponytail artifacts for a readable file

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- summarizes context and ponytail artifacts for a readable file
   - Expected: panel.context_status equals `ready`
   - Expected: panel.ponytail_status equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("summarizes context and ponytail artifacts for a readable file")
val path = _write_tooling_fixture("clean", "fn hello() -> text:\n    \"ok\"\n")
val panel = collect_llm_tooling_artifacts(path, "hello")

expect(panel.context_status).to_equal("ready")
expect(panel.context_lines).to_be_greater_than(0)
expect(panel.context_token_estimate).to_be_greater_than(0)
expect(panel.context_preview).to_contain("hello")
expect(panel.ponytail_status).to_equal("ok")
```

</details>

#### renders text without internal absence markers

- renders text without internal absence markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders text without internal absence markers")
val path = _write_tooling_fixture("smell", "interface FutureThing:\n    pass_todo\n")
val text = render_llm_tooling_artifacts_panel_text(collect_llm_tooling_artifacts(path, "FutureThing"))

expect(text).to_contain("LLM Tooling Artifacts")
expect(text).to_contain("context_status=ready")
expect(text).to_contain("ponytail_status=review")
expect_absence_marker_hidden(text)
```

</details>

#### renders missing files as explicit absence

- renders missing files as explicit absence


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders missing files as explicit absence")
val path = _tooling_fixture_path("missing")
remove_file_if_exists(path)
val text = render_llm_tooling_artifacts_panel_text(collect_llm_tooling_artifacts(path, "missing"))

expect(text).to_contain("context_status=missing")
expect(text).to_contain("ponytail_status=missing")
expect(text).to_contain("ponytail_reason=source unavailable")
expect_absence_marker_hidden(text)
```

</details>

#### escapes html panel fields and preview

- escapes html panel fields and preview
   - Expected: html.split("<tag>").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("escapes html panel fields and preview")
val path = _write_tooling_fixture("html", "fn danger() -> text:\n    \"<tag>&\"\n")
val html = render_llm_tooling_artifacts_panel_html(collect_llm_tooling_artifacts(path, "danger"))

expect(html).to_contain("llm-tooling-artifacts-panel")
expect(html).to_contain("&lt;tag&gt;&amp;")
expect(html.split("<tag>").len()).to_equal(1)
expect_absence_marker_hidden(html)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLM dashboard tooling artifact collector.
- LLM dashboard tooling artifact collector

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `780ecfa4583af4a342a4f3a40ae3e6bad4ca9d6d9cb245903788af3ba7315bd5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `780ecfa4583af4a342a4f3a40ae3e6bad4ca9d6d9cb245903788af3ba7315bd5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `780ecfa4583af4a342a4f3a40ae3e6bad4ca9d6d9cb245903788af3ba7315bd5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.spl
mirror: doc/06_spec/01_unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'summarizes context and ponytail artifacts for a readable file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders text without internal absence markers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_dashboard/collectors/tooling_artifact_collector_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders missing files as explicit absence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
