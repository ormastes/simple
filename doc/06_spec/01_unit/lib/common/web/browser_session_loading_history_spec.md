# Browser Session Loading History Specification

> Tests covering BrowserSession loading history.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Loading History Specification

## Scenarios

### BrowserSession loading history

#### trims stale forward entries before appending a loaded page

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- trims stale forward entries before appending a loaded page
   - Expected: session.history.len() equals `2`
   - Expected: session.current_index equals `1`
   - Expected: session.history[0].url equals `https://example.com/first.html`
   - Expected: session.history[1].url equals `https://example.com/new.html`
   - Expected: session.history[1].source_html equals `<html><body>New</body></html>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("trims stale forward entries before appending a loaded page")
var session = BrowserSession.new()
session.history = [
    BrowserHistoryEntry.create("https://example.com/first.html", "First", "<html><body>First</body></html>"),
    BrowserHistoryEntry.create("https://example.com/second.html", "Second", "<html><body>Second</body></html>"),
    BrowserHistoryEntry.create("https://example.com/stale.html", "Stale", "<html><body>Stale</body></html>")
]
session.current_index = 0
session.current_url = "https://example.com/new.html"
session.current_title = "New"

session._update_history("https://example.com/new.html", "<html><body>New</body></html>", -1, true)

expect(session.history.len()).to_equal(2)
expect(session.current_index).to_equal(1)
expect(session.history[0].url).to_equal("https://example.com/first.html")
expect(session.history[1].url).to_equal("https://example.com/new.html")
expect(session.history[1].source_html).to_equal("<html><body>New</body></html>")
```

</details>

#### bounds retained entries and source bytes without breaking back or forward

- bounds retained entries and source bytes without breaking back or forward
   - Expected: session.history.len() equals `64`
   - Expected: session.history[0].url equals `https://example.com/page-2`
   - Expected: session.current_index equals `63`
   - Expected: session.go_back().is_ok() is true
   - Expected: session.current_url equals `https://example.com/page-64`
   - Expected: session.go_forward().is_ok() is true
   - Expected: session.current_url equals `https://example.com/page-65`
   - Expected: bounded.len() equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("bounds retained entries and source bytes without breaking back or forward")
var session = BrowserSession.new_without_runtime()
var i = 0
while i < 66:
    session.current_url = "https://example.com/page-{i}"
    session.current_title = "Page {i}"
    session._update_history(
        session.current_url, "<p>{i}</p>", -1, true
    )
    i = i + 1
expect(session.history.len()).to_equal(64)
expect(session.history[0].url).to_equal("https://example.com/page-2")
expect(session.current_index).to_equal(63)
expect(session.go_back().is_ok()).to_equal(true)
expect(session.current_url).to_equal("https://example.com/page-64")
expect(session.go_forward().is_ok()).to_equal(true)
expect(session.current_url).to_equal("https://example.com/page-65")

val two_mib = str_repeat("x", 2 * 1024 * 1024)
var bounded: [BrowserHistoryEntry] = []
i = 0
while i < 27:
    bounded = browser_history_push_bounded(
        bounded, bounded.len() - 1,
        BrowserHistoryEntry.create("https://bytes.test/{i}", "", two_mib)
    )
    i = i + 1
expect(bounded.len()).to_equal(25)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_loading_history_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserSession loading history.
- BrowserSession loading history

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `571a7b3fd00741844c990db110bb89cc080ec4f8232b1c64a26ba843bcf307a1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `571a7b3fd00741844c990db110bb89cc080ec4f8232b1c64a26ba843bcf307a1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `571a7b3fd00741844c990db110bb89cc080ec4f8232b1c64a26ba843bcf307a1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/web/browser_session_loading_history_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/browser_session_loading_history_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/web/browser_session_loading_history_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/browser_session_loading_history_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/browser_session_loading_history_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/web/browser_session_loading_history_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trims stale forward entries before appending a loaded page' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_loading_history_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bounds retained entries and source bytes without breaking back or forward' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
