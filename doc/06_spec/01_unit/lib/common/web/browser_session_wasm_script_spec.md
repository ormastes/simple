# Browser Session Wasm Script Specification

> Tests covering BrowserSession WASM script resources.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Wasm Script Specification

## Scenarios

### BrowserSession WASM script resources

#### records inline application wasm beside JavaScript without evaluating it as JS

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records inline application wasm beside JavaScript without evaluating it as JS
   - Expected: session.wasm_modules.len() equals `1`
   - Expected: session.wasm_modules[0].url equals `https://example.com/inline-wasm.html`
   - Expected: session.wasm_modules[0].byte_length equals `8`
   - Expected: session.wasm_modules[0].status equals `validated`
   - Expected: session.warnings.len() equals `0`
   - Expected: _display_js(value) equals `js-before:js-after:function`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records inline application wasm beside JavaScript without evaluating it as JS")
var session = BrowserSession.new()
val html = "<html><body><script>var before = 'js-before';</script><script type='application/wasm'>0061736d01000000</script><script>var after = before + ':js-after';</script></body></html>"
val result = session.open_html("https://example.com/inline-wasm.html", html)

match result:
    Ok(_):
        expect(session.wasm_modules.len()).to_equal(1)
        expect(session.wasm_modules[0].url).to_equal("https://example.com/inline-wasm.html")
        expect(session.wasm_modules[0].byte_length).to_equal(8)
        expect(session.wasm_modules[0].valid).to_be(true)
        expect(session.wasm_modules[0].status).to_equal("validated")
        expect(session.warnings.len()).to_equal(0)
        val js_result = session.eval_script("after + ':' + typeof WebAssembly.instantiate")
        match js_result:
            Ok(value):
                expect(_display_js(value)).to_equal("js-before:js-after:function")
            Err(err):
                fail("Expected JS after inline WASM to evaluate: {err}")
    Err(err):
        fail("Expected inline WASM page to load: {err}")
```

</details>

#### loads external application wasm in script order and resumes later JavaScript

- loads external application wasm in script order and resumes later JavaScript
   - Expected: request.kind equals `wasm`
   - Expected: request.url equals `https://example.com/app.wasm`
   - Expected: request.content_type equals `application/wasm`
   - Expected: session.wasm_modules.len() equals `1`
   - Expected: session.wasm_modules[0].url equals `https://example.com/app.wasm`
   - Expected: session.wasm_modules[0].summary() equals `https://example.com/app.wasm:8:validated`
   - Expected: session.warnings.len() equals `0`
   - Expected: _display_js(value) equals `before:after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("loads external application wasm in script order and resumes later JavaScript")
var session = BrowserSession.new()
val html = "<html><body><script>var order = 'before';</script><script type='application/wasm' src='/app.wasm'></script><script>order = order + ':after';</script></body></html>"
val result = session.open_html("https://example.com/wasm-page.html", html)

match result:
    Ok(_):
        match session.take_pending_request():
            Some(request):
                expect(request.kind).to_equal("wasm")
                expect(request.url).to_equal("https://example.com/app.wasm")
                expect(request.content_type).to_equal("application/wasm")
                val committed = session.commit_network_response(BrowserResponse.create(
                    request_id: request.id,
                    kind: "wasm",
                    url: request.url,
                    status: 200,
                    headers: "Content-Type: application/wasm\n",
                    body: "0061736d01000000",
                    error: ""
                ))
                match committed:
                    Ok(_):
                        expect(session.wasm_modules.len()).to_equal(1)
                        expect(session.wasm_modules[0].url).to_equal("https://example.com/app.wasm")
                        expect(session.wasm_modules[0].summary()).to_equal("https://example.com/app.wasm:8:validated")
                        expect(session.warnings.len()).to_equal(0)
                        val js_result = session.eval_script("order")
                        match js_result:
                            Ok(value):
                                expect(_display_js(value)).to_equal("before:after")
                            Err(err):
                                fail("Expected JS after external WASM to evaluate: {err}")
                    Err(err):
                        fail("Expected external WASM response to commit: {err}")
            nil:
                fail("Expected pending external WASM request")
    Err(err):
        fail("Expected external WASM page to start loading: {err}")
```

</details>

#### reports invalid wasm script payloads without running them as JavaScript

- reports invalid wasm script payloads without running them as JavaScript
   - Expected: session.wasm_modules.len() equals `1`
   - Expected: session.wasm_modules[0].status equals `invalid-wasm-header`
   - Expected: session.warnings.len() equals `1`
   - Expected: _display_js(value) equals `before:after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports invalid wasm script payloads without running them as JavaScript")
var session = BrowserSession.new()
val html = "<html><body><script>var marker = 'before';</script><script type='application/wasm'>0061736d00000000</script><script>marker = marker + ':after';</script></body></html>"
val result = session.open_html("https://example.com/invalid-wasm.html", html)

match result:
    Ok(_):
        expect(session.wasm_modules.len()).to_equal(1)
        expect(session.wasm_modules[0].valid).to_be(false)
        expect(session.wasm_modules[0].status).to_equal("invalid-wasm-header")
        expect(session.warnings.len()).to_equal(1)
        expect(session.warnings[0]).to_contain("wasm module error")
        val js_result = session.eval_script("marker")
        match js_result:
            Ok(value):
                expect(_display_js(value)).to_equal("before:after")
            Err(err):
                fail("Expected JS after invalid WASM to evaluate: {err}")
    Err(err):
        fail("Expected invalid WASM page to load with warning: {err}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_wasm_script_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserSession WASM script resources.
- BrowserSession WASM script resources

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ce8f02884c09755d73abaea7ce5c8624a6290bd675b2c5533ff6e29d755d7c01`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ce8f02884c09755d73abaea7ce5c8624a6290bd675b2c5533ff6e29d755d7c01`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ce8f02884c09755d73abaea7ce5c8624a6290bd675b2c5533ff6e29d755d7c01`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/web/browser_session_wasm_script_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/browser_session_wasm_script_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/web/browser_session_wasm_script_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/browser_session_wasm_script_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/browser_session_wasm_script_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/web/browser_session_wasm_script_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records inline application wasm beside JavaScript without evaluating it as JS' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_wasm_script_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads external application wasm in script order and resumes later JavaScript' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_wasm_script_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports invalid wasm script payloads without running them as JavaScript' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
