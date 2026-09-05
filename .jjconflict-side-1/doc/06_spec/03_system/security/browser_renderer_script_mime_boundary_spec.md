# Browser renderer script MIME boundary

> Exercises final classic-script and module responses through the real

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser renderer script MIME boundary

Exercises final classic-script and module responses through the real

## At a Glance

| Field | Value |
|-------|-------|
| Category | Security |
| Status | Active |
| Source | `test/03_system/security/browser_renderer_script_mime_boundary_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises final classic-script and module responses through the real
capability-bound SBR2 worker boundary. Rejected response bodies must not gain
script, cache, redirect-alias, DOM, global, or cookie authority.

## Scenarios

### Browser renderer script MIME boundary

#### admits only response MIME types authorized for the script mode

- admits only response MIME types authorized for the script mode
   - Protocol capture: after_step
- Admit canonical JavaScript MIME
   - Protocol capture: after_step
- Reject nosniff classic-script MIME
   - Protocol capture: after_step
- Reject redirected module MIME
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: module.request.url equals `https://mime.test/final.js`
- Preserve runtime state after MIME rejection
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 87 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("admits only response MIME types authorized for the script mode")
step("Admit canonical JavaScript MIME")
val admitted = make_script_mime_boundary_fixture()
accept_script_mime_network_response(
    admitted,
    encode_script_mime_network_response(
        admitted, 200,
        "Content-Type: Text/JavaScript; Charset=UTF-8",
        "document.body.innerHTML = '<p id=\"mime-admitted\">yes</p>'"
    )
)
expect(admitted.worker.browser.current_body_html).to_contain(
    "mime-admitted"
)
val sniffed = make_script_mime_boundary_fixture()
accept_script_mime_network_response(
    sniffed,
    encode_script_mime_network_response(
        sniffed, 200, "Content-Type: text/plain",
        "document.body.innerHTML = '<p id=\"mime-sniffed\">yes</p>'"
    )
)
expect(sniffed.worker.browser.current_body_html).to_contain(
    "mime-sniffed"
)
val admitted_module = make_script_mime_boundary_fixture(true)
accept_script_mime_network_response(
    admitted_module,
    encode_script_mime_network_response(
        admitted_module, 200,
        "Content-Type: APPLICATION/JAVASCRIPT; version=1",
        "document.body.innerHTML = " +
        "'<p id=\"mime-module-admitted\">yes</p>'"
    )
)
expect(admitted_module.worker.browser.current_body_html).to_contain(
    "mime-module-admitted"
)

step("Reject nosniff classic-script MIME")
val classic = make_script_mime_boundary_fixture()
val classic_cookie = classic.worker.browser.document_cookie()
accept_script_mime_network_response(
    classic,
    encode_script_mime_network_response(
        classic, 200,
        "Content-Type: text/plain; charset=utf-8\n" +
        "X-Content-Type-Options: NoSniff\n" +
        "Set-Cookie: header=mutated",
        "document.body.innerHTML = 'mime-mutated'; " +
        "document.cookie = 'mime=mutated'; " +
        "globalThis.mimeMutation = 'yes'"
    )
)
expect(classic.worker.browser.warnings).to_contain(
    "external script error: blocked response MIME type"
)
expect_script_mime_state_unchanged(classic, classic_cookie, 0, 0)

step("Reject redirected module MIME")
val module = make_script_mime_boundary_fixture(true)
accept_script_mime_network_response(
    module,
    encode_script_mime_network_response(
        module, 302,
        "Location: https://mime.test/final.js", ""
    )
)
expect(module.request.url).to_equal("https://mime.test/final.js")
val module_cookie = module.worker.browser.document_cookie()
accept_script_mime_network_response(
    module,
    encode_script_mime_network_response(
        module, 200,
        "Content-Type: text/html\nSet-Cookie: header=mutated",
        "document.body.innerHTML = 'mime-mutated'; " +
        "document.cookie = 'mime=mutated'; " +
        "globalThis.mimeMutation = 'yes'"
    )
)
expect(module.worker.browser.warnings).to_contain(
    "module load error: blocked response MIME type"
)

step("Preserve runtime state after MIME rejection")
expect_script_mime_state_unchanged(module, module_cookie, 0, 0)
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
- `REQ-WEB-BROWSER-005`
- `REQ-WEB-BROWSER-010`
- `REQ-WEB-BROWSER-012`
- `REQ-WEB-BROWSER-021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dbddb0b0090ff4187341948c81e2471e7ba9f6d446b194c3def6ce61a8e845e8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dbddb0b0090ff4187341948c81e2471e7ba9f6d446b194c3def6ce61a8e845e8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dbddb0b0090ff4187341948c81e2471e7ba9f6d446b194c3def6ce61a8e845e8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/security/browser_renderer_script_mime_boundary_spec.spl
mirror: doc/06_spec/03_system/security/browser_renderer_script_mime_boundary_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=89; blocker cap makes effective=49
doc/06_spec/03_system/security/browser_renderer_script_mime_boundary_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/security/browser_renderer_script_mime_boundary_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/security/browser_renderer_script_mime_boundary_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/security/browser_renderer_script_mime_boundary_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits only response MIME types authorized for the script mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
