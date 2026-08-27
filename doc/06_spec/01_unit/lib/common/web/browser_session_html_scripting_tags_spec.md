# BrowserSession HTML scripting text projection

> Projects script and noscript content according to the active runtime. This is

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession HTML scripting text projection

Projects script and noscript content according to the active runtime. This is

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Projects script and noscript content according to the active runtime. This is
visible-document evidence, not full JavaScript or pixel-rendering coverage.

## Scenarios

### BrowserSession HTML scripting tag semantics

#### should hide noscript fallback from visible rendering when scripting is enabled

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should hide noscript fallback from visible rendering when scripting is enabled
- Project supported HTML semantics to visible text
   - Expected: session.current_body_html does not contain `Fallback body`
   - Expected: session.render_html_document() does not contain `Fallback body`
   - Expected: "unexpected open error: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should hide noscript fallback from visible rendering when scripting is enabled")
step("Project supported HTML semantics to visible text")
var session = BrowserSession.new()
val result = session.open_html(
    "https://example.com/noscript-enabled",
    "<!DOCTYPE html><html><head><title>NoScript Enabled</title></head><body><p>Visible</p><noscript>Fallback body</noscript></body></html>"
)
match result:
    Ok(_):
        expect(session.source_html).to_contain("<noscript>Fallback body</noscript>")
        expect(session.current_body_html).to_contain("<p>Visible</p>")
        expect(session.current_body_html.contains("Fallback body")).to_equal(false)
        expect(session.render_html_document().contains("Fallback body")).to_equal(false)
    Err(e):
        expect("unexpected open error: {e}").to_equal("")
```

</details>

#### should run script content and hide noscript fallback when scripting is enabled

- should run script content and hide noscript fallback when scripting is enabled
- Project supported HTML semantics to visible text
   - Expected: session.current_body_html equals `Scripted body`
   - Expected: session.current_body_html does not contain `Fallback body`
   - Expected: session.render_html_document() does not contain `Fallback body`
   - Expected: "unexpected open error: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should run script content and hide noscript fallback when scripting is enabled")
step("Project supported HTML semantics to visible text")
var session = BrowserSession.new()
val result = session.open_html(
    "https://example.com/scripted",
    "<!DOCTYPE html><html><head><title>Script Tags</title></head><body><p>Before</p><script>document.body.textContent = 'Scripted body';</script><noscript>Fallback body</noscript></body></html>"
)
match result:
    Ok(_):
        expect(session.source_html).to_contain("<noscript>Fallback body</noscript>")
        expect(session.current_body_html).to_equal("Scripted body")
        expect(session.current_body_html.contains("Fallback body")).to_equal(false)
        expect(session.render_html_document().contains("Fallback body")).to_equal(false)
    Err(e):
        expect("unexpected open error: {e}").to_equal("")
```

</details>

#### should ignore script content and keep noscript fallback visible when runtime is disabled

- should ignore script content and keep noscript fallback visible when runtime is disabled
- Project supported HTML semantics to visible text
   - Expected: session.current_body_html does not contain `Scripted body`
   - Expected: "unexpected open error: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should ignore script content and keep noscript fallback visible when runtime is disabled")
step("Project supported HTML semantics to visible text")
var session = BrowserSession.new_without_runtime()
val result = session.open_html(
    "https://example.com/noscript",
    "<!DOCTYPE html><html><head><title>No Script Tags</title></head><body><p>Before</p><script>document.body.textContent = 'Scripted body';</script><noscript>Fallback body</noscript></body></html>"
)
match result:
    Ok(_):
        expect(session.current_body_html).to_contain("<p>Before</p>")
        expect(session.current_body_html).to_contain("<noscript>Fallback body</noscript>")
        expect(session.current_body_html.contains("Scripted body")).to_equal(false)
        expect(session.warnings).to_contain("scripts are ignored when BrowserSession runtime is disabled")
    Err(e):
        expect("unexpected open error: {e}").to_equal("")
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

- `REQ-SSPEC-UNIT`
- `REQ-WEB-BROWSER-002`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2bc519bfd61110191b0c04259332829f87f69804f72d6b14f6636479629b8ca8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2bc519bfd61110191b0c04259332829f87f69804f72d6b14f6636479629b8ca8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2bc519bfd61110191b0c04259332829f87f69804f72d6b14f6636479629b8ca8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=85 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.spl:26:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should hide noscript fallback from visible rendering when scripting is enabled' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should hide noscript fallback from visible rendering when scripting is enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should run script content and hide noscript fallback when scripting is enabled' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should run script content and hide noscript fallback when scripting is enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should ignore script content and keep noscript fallback visible when runtime is disabled' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should ignore script content and keep noscript fallback visible when runtime is disabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
