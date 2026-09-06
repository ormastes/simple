# browser_session_js_closure_scope_spec

> <html><body><script>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_session_js_closure_scope_spec

<html><body><script>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/web/browser_session_js_closure_scope_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

<html><body><script>
            var out = 'unset';
            fetch('/t').then(function(r) {
                return r.text().then(function(v) {
                    out = v + ':' + (typeof r) + ':' + r.status;
                });
            });
            </script></body></html>

## Scenarios

### JS engine lexical scope chain

#### row G: reads a function's own parameter directly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- row G: reads a function's own parameter directly
   - Expected: _eval_script_html("function f(x) { out = '' + x; } f(5);") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("row G: reads a function's own parameter directly")
expect(_eval_script_html("function f(x) { out = '' + x; } f(5);")).to_equal("5")
```

</details>

#### row I: a nested callback reads the enclosing function's parameter

- row I: a nested callback reads the enclosing function's parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("row I: a nested callback reads the enclosing function's parameter")
expect(
    _eval_script_html(
        "function f(x) { [1].forEach(function(v) { out = '' + x; }); } f(5);"
    )
).to_equal("5")
```

</details>

#### row H: a nested callback reads the enclosing function's var local and parameter

- row H: a nested callback reads the enclosing function's var local and parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("row H: a nested callback reads the enclosing function's var local and parameter")
expect(
    _eval_script_html(
        "function f(x) { var y = x; [1].forEach(function(v) { out = '' + y + ':' + x; }); } f(5);"
    )
).to_equal("5:5")
```

</details>

#### row J: the same capture works for a function expression

- row J: the same capture works for a function expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("row J: the same capture works for a function expression")
expect(
    _eval_script_html(
        "var g = function(x) { [1].forEach(function(v) { out = '' + x; }); }; g(5);"
    )
).to_equal("5")
```

</details>

#### row E: a promise job callback captures the enclosing parameter

- row E: a promise job callback captures the enclosing parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("row E: a promise job callback captures the enclosing parameter")
expect(
    _eval_script_html(
        "function f(x) { return Promise.resolve(1).then(function(v) { out = '' + (typeof x) + ':' + x; }); } f(5);"
    )
).to_equal("number:5")
```

</details>

#### row A: a nested then callback keeps the enclosing Response in scope

- row A: a nested then callback keeps the enclosing Response in scope
   - Expected: request.url equals `https://example.com/t`
   - Expected: _display_js(value) equals `alpha:object:200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("row A: a nested then callback keeps the enclosing Response in scope")
var session = BrowserSession.new()
session.open_html(
    "https://example.com/app",
    """
    <html><body><script>
    var out = 'unset';
    fetch('/t').then(function(r) {
        return r.text().then(function(v) {
            out = v + ':' + (typeof r) + ':' + r.status;
        });
    });
    </script></body></html>
    """
)
match session.take_pending_request():
    Some(request):
        expect(request.url).to_equal("https://example.com/t")
        match session.commit_network_response(
            BrowserResponse.create(
                request_id: request.id,
                kind: "fetch",
                url: request.url,
                status: 200,
                headers: "",
                body: "alpha",
                error: ""
            )
        ):
            Ok(_): expect(request.kind).to_equal("fetch")
            Err(e): fail("Expected fetch response commit to succeed: {e}")
    nil:
        fail("Expected a pending fetch request for https://example.com/t")

match session.eval_script("out"):
    Ok(value):
        expect(_display_js(value)).to_equal("alpha:object:200")
    Err(e):
        fail("Expected nested-then capture probe to evaluate: {e}")
```

</details>

#### an inner binding shadows the enclosing one and does not leak outward

- an inner binding shadows the enclosing one and does not leak outward


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an inner binding shadows the enclosing one and does not leak outward")
expect(
    _eval_script_html(
        "function f(x) { [1].forEach(function(v) { var x = 9; }); out = '' + x; } f(5);"
    )
).to_equal("5")
```

</details>

#### an assignment in a nested callback writes through to the enclosing local

- an assignment in a nested callback writes through to the enclosing local


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an assignment in a nested callback writes through to the enclosing local")
expect(
    _eval_script_html(
        "function f(x) { var y = 1; [1].forEach(function(v) { y = x + 1; }); out = '' + y; } f(5);"
    )
).to_equal("6")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5e003ed238993356ae91f9d89e5dcf05fdef9978fa9991509ad6b3673a99b64f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e003ed238993356ae91f9d89e5dcf05fdef9978fa9991509ad6b3673a99b64f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e003ed238993356ae91f9d89e5dcf05fdef9978fa9991509ad6b3673a99b64f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/web/browser_session_js_closure_scope_spec.spl
mirror: doc/06_spec/unit/lib/common/web/browser_session_js_closure_scope_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/web/browser_session_js_closure_scope_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/web/browser_session_js_closure_scope_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/web/browser_session_js_closure_scope_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'row G: reads a function's own parameter directly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/web/browser_session_js_closure_scope_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'row I: a nested callback reads the enclosing function's parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/web/browser_session_js_closure_scope_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'row H: a nested callback reads the enclosing function's var local and parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
