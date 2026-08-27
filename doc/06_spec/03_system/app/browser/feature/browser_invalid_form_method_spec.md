# browser_invalid_form_method_spec

> Invalid HTML form-method fallback system specification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_invalid_form_method_spec

"""
Invalid HTML form-method fallback system specification.

**Requirements:**
- REQ-WEB-BROWSER-007: submit callbacks precede the default form action.
- REQ-WEB-BROWSER-008: a public button click activates its owning form.
- REQ-WEB-BROWSER-010: missing, empty, and invalid method tokens use GET.
- REQ-WEB-BROWSER-012: unsupported transports remain blocked after fallback.
- REQ-WEB-BROWSER-021: executable evidence has a complete mirrored manual.

The selected profile supports GET and POST. Invalid method tokens are not a
transport permission and therefore fall back to GET before the independent
navigation boundary evaluates the action URL.
"""

fn setup_invalid_form_method_fixture() -> BrowserSession:
    var session = BrowserSession.new()
    expect(session.open_html(
        "https://example.test/form",
        "<html><body><form id='profile' action='/save' method='patch' " +
        "onsubmit='set-attr:data-submitted=yes'>" +
        "<input name='name' value='Ada'>" +
        "<button id='save' name='intent' value='save'>Save</button>" +
        "</form></body></html>"
    ).is_ok()).to_equal(true)
    session

fn check_invalid_method_uses_get(session: BrowserSession):
    val callbacks_before = session.dom_callback_count
    val dispatch = session.dispatch_dom_event("save", "click", true, true)
    expect(dispatch.default_action).to_equal("button-activate")
    expect(dispatch.default_action_allowed).to_equal(true)
    expect(session.dom_callback_count).to_equal(callbacks_before + 1)
    val root = session.dom_root()
    val identity_index = system_browser_dom_identity_index(session)
    val form_path = be_dom_path_for_route(
        root, identity_index, system_dom_route(identity_index, "profile")
    )
    expect(be_dom_get_attr(
        form_path[form_path.len() - 1], "data-submitted"
    )).to_equal("yes")
    match session.take_pending_request():
        Some(request):
            expect(request.method).to_equal("GET")
            expect(request.url).to_equal(
                "https://example.test/save?name=Ada&intent=save"
            )
            expect(request.body).to_equal("")
            expect(request.content_type).to_equal("")
        nil:
            fail("invalid form method did not produce GET navigation")

    var canceled = BrowserSession.new()
    expect(canceled.open_html(
        "https://example.test/form",
        "<form action='/blocked' method='patch' onsubmit='prevent-default'>" +
        "<button id='blocked'>Blocked</button></form>"
    ).is_ok()).to_equal(true)
    val callbacks_before_cancel = canceled.dom_callback_count
    val canceled_click = canceled.dispatch_dom_event(
        "blocked", "click", true, true
    )
    expect(canceled_click.default_action).to_equal("button-activate")
    expect(canceled.dom_callback_count).to_equal(
        callbacks_before_cancel + 1
    )
    expect(canceled.has_pending_requests()).to_equal(false)

    for declaration in ["", " method=''"]:
        var fallback = BrowserSession.new()
        expect(fallback.open_html(
            "https://example.test/form",
            "<form action='/fallback'{declaration}>" +
            "<input name='q' value='simple'><button id='go'>Go</button></form>"
        ).is_ok()).to_equal(true)
        val _ = fallback.dispatch_dom_event("go", "click", true, true)
        match fallback.take_pending_request():
            Some(request):
                expect(request.method).to_equal("GET")
                expect(request.url).to_equal(
                    "https://example.test/fallback?q=simple"
                )
                expect(request.body).to_equal("")
            nil:
                fail("missing or empty form method did not use GET")

    for override in ["", "delete"]:
        var fallback = BrowserSession.new()
        expect(fallback.open_html(
            "https://example.test/form",
            "<form action='/override' method='post'>" +
            "<input name='q' value='simple'><button id='go' " +
            "formmethod='{override}'>Go</button></form>"
        ).is_ok()).to_equal(true)
        val _ = fallback.dispatch_dom_event("go", "click", true, true)
        match fallback.take_pending_request():
            Some(request):
                expect(request.method).to_equal("GET")
                expect(request.url).to_equal(
                    "https://example.test/override?q=simple"
                )
                expect(request.body).to_equal("")
            nil:
                fail("empty or invalid submitter method did not override with GET")

fn check_valid_methods_unchanged():
    var get_session = BrowserSession.new()
    expect(get_session.open_html(
        "https://example.test/form",
        "<form action='/find?source=form' method='GET'>" +
        "<input name='q' value='simple web'><button id='find'>Find</button></form>"
    ).is_ok()).to_equal(true)
    val _ = get_session.dispatch_dom_event("find", "click", true, true)
    match get_session.take_pending_request():
        Some(request):
            expect(request.method).to_equal("GET")
            expect(request.url).to_equal(
                "https://example.test/find?source=form&q=simple+web"
            )
            expect(request.body).to_equal("")
            expect(request.content_type).to_equal("")
        nil:
            fail("valid GET form did not navigate")

    var post_session = BrowserSession.new()
    expect(post_session.open_html(
        "https://example.test/form",
        "<form action='/save' method='POST'>" +
        "<input name='q' value='simple web'><button id='save'>Save</button></form>"
    ).is_ok()).to_equal(true)
    val _ = post_session.dispatch_dom_event("save", "click", true, true)
    match post_session.take_pending_request():
        Some(request):
            expect(request.method).to_equal("POST")
            expect(request.url).to_equal("https://example.test/save")
            expect(request.body).to_equal("q=simple+web")
            expect(request.content_type).to_equal(
                "application/x-www-form-urlencoded"
            )
        nil:
            fail("valid POST form did not navigate")

fn check_transport_policy_still_fails_closed():
    for html in [
        "<form method='dialog' onsubmit='set-attr:data-submitted=yes'>" +
        "<button id='go'>Go</button></form>",
        "<form method='post' onsubmit='set-attr:data-submitted=yes'>" +
        "<button id='go' formmethod='dialog'>Go</button></form>"
    ]:
        var dialog_session = BrowserSession.new()
        expect(dialog_session.open_html(
            "https://example.test/form", html
        ).is_ok()).to_equal(true)
        val callbacks_before_dialog = dialog_session.dom_callback_count
        val dialog_dispatch = dialog_session.dispatch_dom_event(
            "go", "click", true, true
        )
        expect(dialog_dispatch.default_action_allowed).to_equal(true)
        expect(dialog_session.dom_callback_count).to_equal(
            callbacks_before_dialog + 1
        )
        expect(dialog_session.has_pending_requests()).to_equal(false)
        expect(dialog_session.warnings.join("|")).to_contain(
            "unsupported form method: dialog"
        )

    var session = BrowserSession.new()
    expect(session.open_html(
        "https://example.test/form",
        "<form action='file:///etc/passwd' method='patch' " +
        "onsubmit='set-attr:data-submitted=yes'>" +
        "<input name='q' value='simple'><button id='go'>Go</button></form>"
    ).is_ok()).to_equal(true)
    val callbacks_before = session.dom_callback_count
    val dispatch = session.dispatch_dom_event("go", "click", true, true)
    expect(dispatch.default_action_allowed).to_equal(true)
    expect(session.dom_callback_count).to_equal(callbacks_before + 1)
    expect(session.has_pending_requests()).to_equal(false)
    expect(session.warnings.join("|")).to_contain(
        "form navigation blocked: unsupported scheme: file"
    )
    expect(session.warnings.join("|").contains(
        "unsupported form method"
    )).to_equal(false)

describe "BrowserSession invalid form method fallback":
    # @req REQ-WEB-BROWSER-007 REQ-WEB-BROWSER-008 REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-012 REQ-WEB-BROWSER-021
    it "should use GET for invalid method tokens without widening transport":
        step("Submit a form with an invalid method")
        val fixture = setup_invalid_form_method_fixture()

        step("Observe canonical GET encoding")
        check_invalid_method_uses_get(fixture)

        step("Submit valid GET and POST controls")
        check_valid_methods_unchanged()

        step("Reject transport outside the form-method fallback")
        check_transport_policy_still_fails_closed()
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

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-007`
- `REQ-WEB-BROWSER-008`
- `REQ-WEB-BROWSER-010`
- `REQ-WEB-BROWSER-012`
- `REQ-WEB-BROWSER-021`
- `REQ-WEB-BROWSER-007:`
- `REQ-WEB-BROWSER-008:`
- `REQ-WEB-BROWSER-010:`
- `REQ-WEB-BROWSER-012:`
- `REQ-WEB-BROWSER-021:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1f87a72a5325587546db2069152de95ad1f68611ebb61721df90a9a691380ab3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f87a72a5325587546db2069152de95ad1f68611ebb61721df90a9a691380ab3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f87a72a5325587546db2069152de95ad1f68611ebb61721df90a9a691380ab3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/browser/feature/browser_invalid_form_method_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_invalid_form_method_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=85 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/app/browser/feature/browser_invalid_form_method_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_invalid_form_method_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_invalid_form_method_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/app/browser/feature/browser_invalid_form_method_spec.spl:205:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should use GET for invalid method tokens without widening transport' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/browser/feature/browser_invalid_form_method_spec.spl:205:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use GET for invalid method tokens without widening transport' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
