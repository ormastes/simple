# browser_session_script_navigation_scheme_security_spec

> BrowserSession script-navigation reference security.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_session_script_navigation_scheme_security_spec

BrowserSession script-navigation reference security.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_script_navigation_scheme_security_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

BrowserSession script-navigation reference security.

Location and History API navigation share one strict URL-reference policy:
trusted explicit schemes stay explicit, relative references resolve against the
active document, and opaque or unknown schemes never mutate browser state.

## Scenarios

### BrowserSession script-navigation reference security

#### should share strict scheme and reference policy across location and history

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should share strict scheme and reference policy across location and history
- Commit stable sessions for blocked and valid controls
- Reject opaque unknown and cross-origin history targets
- Preserve state proposals runtime values and network
   - Expected: blocked_session.current_url equals `stable_url`
   - Expected: blocked_session.document_url equals `stable_url`
   - Expected: blocked_session.current_title equals `Stable`
   - Expected: blocked_session.history.len() equals `1`
   - Expected: blocked_session.current_index equals `0`
   - Expected: blocked_session.history_proposal_action equals ``
   - Expected: blocked_session.history_proposal_url_kind equals ``
   - Expected: blocked_session.history_proposal_raw_url equals ``
   - Expected: href equals `stable_url`
- Resolve valid references HTTPS history and traversal
   - Expected: reference_session.history.len() equals `10`
   - Expected: history_session.history.len() equals `3`
   - Expected: history_session.current_url equals `stable_url`
   - Expected: history_session.history.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 136 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should share strict scheme and reference policy across location and history")
step("Commit stable sessions for blocked and valid controls")
val stable_url = "https://stable.test/dir/page"
val stable_html = (
    "<html><head><title>Stable</title></head>" +
    "<body>stable</body></html>"
)
var blocked_session = BrowserSession.new()
var reference_session = BrowserSession.new()
var history_session = BrowserSession.new()
expect(blocked_session.open_html(
    stable_url, stable_html
).is_ok()).to_be(true)
expect(reference_session.open_html(
    stable_url, stable_html
).is_ok()).to_be(true)
expect(history_session.open_html(
    stable_url, stable_html
).is_ok()).to_be(true)

step("Reject opaque unknown and cross-origin history targets")
val blocked_urls = [
    "data:text/html,blocked",
    "javascript:alert(1)",
    "file:///etc/passwd",
    "custom:payload",
    "mailto:user@example.test",
    "unknown://host/path"
]
for blocked_url in blocked_urls:
    expect(blocked_session.eval_script(
        "location.assign('" + blocked_url + "')"
    ).is_ok()).to_be(true)
    expect(blocked_session.eval_script(
        "history.pushState(1, '', '" + blocked_url + "')"
    ).is_ok()).to_be(true)
    expect(blocked_session.eval_script(
        "history.replaceState(2, '', '" + blocked_url + "')"
    ).is_ok()).to_be(true)
expect(blocked_session.eval_script(
    "history.pushState(3, '', 'https://evil.test/x')"
).is_ok()).to_be(true)
expect(blocked_session.eval_script(
    "history.replaceState(4, '', '//evil.test/y')"
).is_ok()).to_be(true)

step("Preserve state proposals runtime values and network")
expect(blocked_session.current_url).to_equal(stable_url)
expect(blocked_session.document_url).to_equal(stable_url)
expect(blocked_session.current_title).to_equal("Stable")
expect(blocked_session.current_body_html).to_contain("stable")
expect(blocked_session.history.len()).to_equal(1)
expect(blocked_session.current_index).to_equal(0)
expect(blocked_session.history_proposal_action).to_equal("")
expect(blocked_session.history_proposal_url_kind).to_equal("")
expect(blocked_session.history_proposal_raw_url).to_equal("")
match blocked_session.eval_script("location.href"):
    Ok(JsValue.String(href)):
        expect(href).to_equal(stable_url)
    _:
        fail("Expected rejected navigation to restore runtime location")
match blocked_session.eval_script("history.state === null"):
    Ok(JsValue.Boolean(is_null)):
        expect(is_null).to_be(true)
    _:
        fail("Expected rejected History API calls to preserve state")
expect(blocked_session.warnings.join("|")).to_contain(
    "script navigation blocked: unsupported navigation scheme"
)
expect(blocked_session.warnings.join("|")).to_contain(
    "invalid history URL blocked"
)
expect(blocked_session.has_pending_requests()).to_be(false)
expect(blocked_session.take_pending_request()).to_be_nil()
expect(blocked_session.can_stop_loading()).to_be(false)

step("Resolve valid references HTTPS history and traversal")
val references = [
    "child", "next.html", "/root", "./leaf",
    "../up", "?q=1", "#frag", "//next.test/x"
]
val expected_urls = [
    "https://stable.test/dir/child",
    "https://stable.test/dir/next.html",
    "https://stable.test/root",
    "https://stable.test/dir/leaf",
    "https://stable.test/up",
    "https://stable.test/dir/page?q=1",
    "https://stable.test/dir/page#frag",
    "https://next.test/x"
]
var reference_index = 0
while reference_index < references.len():
    expect(reference_session.eval_script(
        "location.assign('" + references[reference_index] + "')"
    ).is_ok()).to_be(true)
    expect(reference_session.current_url).to_equal(
        expected_urls[reference_index]
    )
    reference_index = reference_index + 1
expect(reference_session.eval_script(
    "location.assign('https://next.test/final')"
).is_ok()).to_be(true)
expect(reference_session.current_url).to_equal(
    "https://next.test/final"
)
expect(reference_session.history.len()).to_equal(10)
expect(reference_session.has_pending_requests()).to_be(false)

expect(history_session.eval_script(
    "history.pushState(1, '', 'child')"
).is_ok()).to_be(true)
expect(history_session.eval_script(
    "history.pushState(2, '', '/two')"
).is_ok()).to_be(true)
expect(history_session.eval_script(
    "history.replaceState(3, '', '//stable.test/final')"
).is_ok()).to_be(true)
expect(history_session.history.len()).to_equal(3)
expect(history_session.current_url).to_equal(
    "https://stable.test/final"
)
expect(history_session.go_back().is_ok()).to_be(true)
expect(history_session.current_url).to_equal(
    "https://stable.test/dir/child"
)
expect(history_session.go_back().is_ok()).to_be(true)
expect(history_session.current_url).to_equal(stable_url)
expect(history_session.go_forward().is_ok()).to_be(true)
expect(history_session.go_forward().is_ok()).to_be(true)
expect(history_session.current_url).to_equal(
    "https://stable.test/final"
)
expect(history_session.history.len()).to_equal(3)
expect(history_session.has_pending_requests()).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `e2536eda5d9411be5c4dae50d28063ba73b5d7ee1696c1814b5eaeef1429cef1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e2536eda5d9411be5c4dae50d28063ba73b5d7ee1696c1814b5eaeef1429cef1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e2536eda5d9411be5c4dae50d28063ba73b5d7ee1696c1814b5eaeef1429cef1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/web/browser_session_script_navigation_scheme_security_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/browser_session_script_navigation_scheme_security_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=95 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/web/browser_session_script_navigation_scheme_security_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/browser_session_script_navigation_scheme_security_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/browser_session_script_navigation_scheme_security_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/web/browser_session_script_navigation_scheme_security_spec.spl:29:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should share strict scheme and reference policy across location and history' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_script_navigation_scheme_security_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should share strict scheme and reference policy across location and history' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
