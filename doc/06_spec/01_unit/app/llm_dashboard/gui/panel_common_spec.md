# Panel Common Specification

> Tests covering Shared panel CSS + HTML chrome (gui/*_panel_html generators).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Panel Common Specification

## Scenarios

### Shared panel CSS + HTML chrome (gui/*_panel_html generators)

#### defines the shared card/status/empty/error tokens and classes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines the shared card/status/empty/error tokens and classes


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("defines the shared card/status/empty/error tokens and classes")
val css = generate_panel_common_css()

expect(css).to_contain("--panel-ok")
expect(css).to_contain("--panel-warn")
expect(css).to_contain("--panel-critical")
expect(css).to_contain(".panel-card")
expect(css).to_contain(".panel-empty")
expect(css).to_contain(".panel-error")
expect(css).to_contain(".panel-toolbar")
```

</details>

#### collapses grids and the two-column body to a single column narrow

- collapses grids and the two-column body to a single column narrow


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("collapses grids and the two-column body to a single column narrow")
val css = generate_panel_common_css()

expect(css).to_contain("@media (max-width: 700px)")
expect(css).to_contain(".main-content { flex-direction: column; }")
```

</details>

#### builds a manual-refresh + updated-stamp toolbar for a named panel

- builds a manual-refresh + updated-stamp toolbar for a named panel


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("builds a manual-refresh + updated-stamp toolbar for a named panel")
val toolbar = panel_toolbar_html("stats")

expect(toolbar).to_contain("panel-toolbar")
expect(toolbar).to_contain("data-panel-updated=\"stats\"")
expect(toolbar).to_contain("refreshPanel('stats')")
expect(toolbar).to_contain("updated just now")
```

</details>

#### wraps a panel body with the toolbar and a stable #panel-<name> mount point

- wraps a panel body with the toolbar and a stable #panel-<name> mount point


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("wraps a panel body with the toolbar and a stable #panel-<name> mount point")
val wrapped = panel_wrap_html("cache", "<p>body</p>")

expect(wrapped).to_contain("data-panel-wrap=\"cache\"")
expect(wrapped).to_contain("id=\"panel-cache\"")
expect(wrapped).to_contain("<p>body</p>")
expect(wrapped).to_contain("refreshPanel('cache')")
```

</details>

#### escapes the panel name so it cannot break out of the HTML attribute

- escapes the panel name so it cannot break out of the HTML attribute
   - Expected: wrapped.split("\"><script>").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("escapes the panel name so it cannot break out of the HTML attribute")
val wrapped = panel_wrap_html("x\"><script>", "body")

expect(wrapped).to_contain("&quot;")
expect(wrapped.split("\"><script>").len()).to_equal(1)
```

</details>

#### renders a styled empty state

- renders a styled empty state


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders a styled empty state")
val empty = panel_empty_html("No MCP server calls captured yet.")

expect(empty).to_contain("panel-empty")
expect(empty).to_contain("No MCP server calls captured yet.")
```

</details>

#### renders a styled 'collector unavailable' error state with the reason

- renders a styled 'collector unavailable' error state with the reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders a styled 'collector unavailable' error state with the reason")
val error_html = panel_error_html("timed out")

expect(error_html).to_contain("panel-error")
expect(error_html).to_contain("collector unavailable: timed out")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_dashboard/gui/panel_common_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Shared panel CSS + HTML chrome (gui/*_panel_html generators).
- Shared panel CSS + HTML chrome (gui/*_panel_html generators)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `830e8f52ef9a66224489bc5fcd70cd7b7eddcf35366ad835347fa42423790634`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `830e8f52ef9a66224489bc5fcd70cd7b7eddcf35366ad835347fa42423790634`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `830e8f52ef9a66224489bc5fcd70cd7b7eddcf35366ad835347fa42423790634`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/llm_dashboard/gui/panel_common_spec.spl
mirror: doc/06_spec/01_unit/app/llm_dashboard/gui/panel_common_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_dashboard/gui/panel_common_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_dashboard/gui/panel_common_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_dashboard/gui/panel_common_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_dashboard/gui/panel_common_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines the shared card/status/empty/error tokens and classes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_dashboard/gui/panel_common_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collapses grids and the two-column body to a single column narrow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_dashboard/gui/panel_common_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a manual-refresh + updated-stamp toolbar for a named panel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
