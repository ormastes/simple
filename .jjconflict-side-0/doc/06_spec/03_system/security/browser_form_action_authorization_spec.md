# Browser Form-Action Authorization

> Proves that an authenticated HTTPS document cannot submit live form data past

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 2 | 2 | 0 | 0 |

## At a Glance

| Field | Value |
|-------|-------|
| Category | Security |
| Status | Active |
| Source | `test/03_system/security/browser_form_action_authorization_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves that an authenticated HTTPS document cannot submit live form data past
its committed CSP form-action capability, while an authorized same-origin form
continues through the canonical browser request path. Rendering evidence stays
on WebIR -> DrawIrComposition -> Engine2D pixels.

## Scenarios

### REQ-WEB-BROWSER-012: CSP form-action authorization

2. **Apply origin and sandbox policy**
   - Confirm the response CSP permits form mechanics and same-origin state.
   - Confirm `form-action 'none'` remains the destination authority.
   - Require the WebIR-derived `DrawIrComposition` batch's complete source
     metadata to identify the HTML AST owner and the stable `authorized`
     command to occupy `(0,0,8,4)`.
   - Require all 32 framebuffer pixels to equal the fixed blue ARGB oracle.

3. **Reject invalid transport or capability state**
   - Activate the cross-origin POST form through implicit Enter submission.
   - Resolve the dispatched typed route back to the indexed `send` author ID.
   - Require a CSP denial warning, zero queued requests, and no queued body.
   - Separately resolve the `save` route and prove `form-action 'self'` queues
     the authorized same-origin POST with its exact live body.

4. **Render only the authorized document**
   - Keep the HTTPS account URL and visible profile document committed.
   - Recheck exact command geometry, source identity, color, and all 32 pixels
     against fixed values rather than comparing the renderer to itself.

## Pass/Fail Oracle

PASS requires the denied destination and `token-123` body never to enter a
pending request, the same-origin `/save` POST to remain functional, and the
authorized document's canonical command and complete framebuffer to match the
fixed oracle. Author IDs are evidence projections from generation-qualified
dispatch routes, never dispatch authority. Any cross-origin queued request,
document replacement, geometry or source mismatch, or pixel mismatch is FAIL.

### should make hosted renderer document navigation inherit form-action

1. **Bind the parent-owned policy to a renderer navigation**
   - The hosted broker copies committed `form-action 'self'` and the source
     document URL into its host-only permit.

2. **Deny an untrusted renderer target before it becomes a permit**
   - A renderer GET to a collector under `form-action 'none'` has no permit.
     Untyped renderer documents intentionally constrain links with form-action
     too, because a GET form cannot safely be distinguished from a forged link.

The hosted policy companion additionally retains that host-only authority on
an allowed redirect and rejects a denied redirect before cookies, HSTS, history,
or a successor permit can change.

## Companion Integration Controls

The focused browser-session integration spec additionally fixes the CSP
source-list boundary: scheme-less and wildcard hosts, default/explicit/wildcard
ports, path matching, HTTP-to-HTTPS scheme upgrades, downgrade rejection, and
malformed host sources. Its redirect chain also proves that a denied target is
authorized before `Set-Cookie` or `Strict-Transport-Security` can change state,
while the current URL, HTML, and pending-request queue remain unchanged.

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-WEB-BROWSER-012
```

</details>

#### should make hosted renderer document navigation inherit form-action

- should make hosted renderer document navigation inherit form-action
- Bind the parent-owned policy to a renderer navigation
- Deny an untrusted renderer target before it becomes a permit


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should make hosted renderer document navigation inherit form-action")
step("Bind the parent-owned policy to a renderer navigation")
var broker = HostedBrowserRendererProcess.create(12, 8, 4)
broker.document_url = "https://account.test/profile"
broker.document_origin = "https://account.test"
broker.document_csp_policy = "form-action 'self'"
broker.document_csp_ready = true
expect(broker.authorize_renderer_navigation(
    BrowserRendererNetworkDecodeResult(
        ok: true, reason: "ok", reply_to_request_id: 1,
        request_id: "form-save", kind: "document",
        url: "https://account.test/save", method: "POST",
        headers: "", body: "name=Ada",
        content_type: "application/x-www-form-urlencoded",
        credentials: "include", script_cookie_writes: [], status: 0,
        error: "", initiator_origin: "https://account.test"
    )
)).to_be(true)
expect(broker.navigation_permit.form_action_policy).to_equal(
    "form-action 'self'"
)
expect(broker.navigation_permit.form_action_document_url).to_equal(
    "https://account.test/profile"
)

step("Deny an untrusted renderer target before it becomes a permit")
broker.navigation_permit.active = false
broker.document_csp_policy = "form-action 'none'"
expect(broker.authorize_renderer_navigation(
    BrowserRendererNetworkDecodeResult(
        ok: true, reason: "ok", reply_to_request_id: 2,
        request_id: "forged-get", kind: "document",
        url: "https://collector.test/capture?secret=token",
        method: "GET", headers: "", body: "", content_type: "",
        credentials: "include", script_cookie_writes: [], status: 0,
        error: "", initiator_origin: "https://account.test"
    )
)).to_be(false)
expect(broker.navigation_permit.active).to_be(false)
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
- `REQ-WEB-BROWSER-012`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3ee005b0ba0291671e97055d25ea715dd18c992e9b4e06627b375ea0a4f27ed4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3ee005b0ba0291671e97055d25ea715dd18c992e9b4e06627b375ea0a4f27ed4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3ee005b0ba0291671e97055d25ea715dd18c992e9b4e06627b375ea0a4f27ed4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/security/browser_form_action_authorization_spec.spl
mirror: doc/06_spec/03_system/security/browser_form_action_authorization_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/security/browser_form_action_authorization_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/security/browser_form_action_authorization_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/security/browser_form_action_authorization_spec.spl:60:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should keep form data and rendering inside the authorized origin' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/security/browser_form_action_authorization_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep form data and rendering inside the authorized origin' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/security/browser_form_action_authorization_spec.spl:198:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should make hosted renderer document navigation inherit form-action' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/security/browser_form_action_authorization_spec.spl:198:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should make hosted renderer document navigation inherit form-action' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
