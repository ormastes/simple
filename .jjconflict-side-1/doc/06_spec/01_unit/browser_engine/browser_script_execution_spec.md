# Browser Script Execution Wiring

> Proves the production browser render path actually EXECUTES page scripts

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Script Execution Wiring

Proves the production browser render path actually EXECUTES page scripts

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/browser_script_execution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the production browser render path actually EXECUTES page scripts
before paint: a `<script>` that mutates the DOM must be visible in the
post-script rendered document, not just collected and discarded.

Covers the three script lanes the engine ships:
- JavaScript (in-process JS runtime, DOM mutations flushed to the session DOM)
- Simple script (`text/simple`, constrained in-process evaluator)
- WebAssembly (`application/wasm`) — the engine VALIDATES and RECORDS wasm
  modules and exposes `WebAssembly` globals to JS, but does not execute wasm
  bytecode; that explicit recorded status is asserted here, never skipped.

This is the wiring gate for
doc/08_tracking/bug/browser_script_execution_not_wired_2026-05-10.md:
`app.browser.render_adapter.browser_engine_pixels_at` now routes any document
containing `<script>` through this same BrowserSession path.

## Scenarios

### browser script execution in the render path

#### reflects a JavaScript DOM text and title mutation in the rendered document

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reflects a JavaScript DOM text and title mutation in the rendered document
- load a page whose inline JS rewrites body text and title
- render the post-script document


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("reflects a JavaScript DOM text and title mutation in the rendered document")
"""A page whose inline JS rewrites the body and title renders the
script's output, proving JS ran against the live DOM before paint."""
step("load a page whose inline JS rewrites body text and title")
var session = BrowserSession.new()
val html = "<html><head><title>Before</title></head><body>" +
    "<div id='greet'>static-text</div>" +
    "<script>document.body.innerHTML = " +
    "'<div id=\"greet\">js-mutated-text</div>';" +
    "document.title = 'AfterScript';</script></body></html>"
match session.open_html("https://example.test/js-exec.html", html):
    Ok(_): pass_do_nothing
    Err(err): fail("expected JS page to load: {err}")

step("render the post-script document")
val rendered = session.render_html_document()

assert_contains(rendered, "js-mutated-text")
assert_true(not rendered.contains("static-text"))
assert_contains(rendered, "AfterScript")
```

</details>

#### reflects a JavaScript inline style mutation in the rendered document

- reflects a JavaScript inline style mutation in the rendered document
- load a page whose JS sets the body element background color
- render the post-script document


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("reflects a JavaScript inline style mutation in the rendered document")
"""A script that sets element style must change the styled output the
renderer sees, not only an internal dirty flag."""
step("load a page whose JS sets the body element background color")
# NOTE: per-element `getElementById(..).style.X = v` does not flush to
# the serialized DOM yet — the body element is the style surface the
# host mutation plan supports today (gap recorded in
# doc/08_tracking/bug/browser_script_execution_not_wired_2026-05-10.md).
var session = BrowserSession.new()
val html = "<html><body><div id='stage'>stage</div>" +
    "<script>document.body" +
    ".style.backgroundColor = 'rgb(220, 38, 38)';</script>" +
    "</body></html>"
match session.open_html("https://example.test/js-style.html", html):
    Ok(_): pass_do_nothing
    Err(err): fail("expected JS style page to load: {err}")

step("render the post-script document")
val rendered = session.render_html_document()

assert_contains(rendered, "background-color")
assert_contains(rendered, "220, 38, 38")
```

</details>

#### reflects a Simple script title and body mutation in the rendered document

- reflects a Simple script title and body mutation in the rendered document
- load a page carrying a text/simple script
- inspect committed document state and rendered output
   - Expected: session.current_title equals `SimpleScriptTitle`
   - Expected: session.current_body_html equals `simple-script-mutated-body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("reflects a Simple script title and body mutation in the rendered document")
"""A `text/simple` script's title/body commands mutate the same
session document the renderer paints."""
step("load a page carrying a text/simple script")
var session = BrowserSession.new()
# No authored <title>: markup titles are re-extracted at load finalize
# and would override the script's title command.
val html = "<html><body>" +
    "<script type='text/simple'>title \"SimpleScriptTitle\"\n" +
    "body_text \"simple-script-mutated-body\"</script></body></html>"
match session.open_html("https://example.test/simple-exec.html", html):
    Ok(_): pass_do_nothing
    Err(err): fail("expected Simple script page to load: {err}")

step("inspect committed document state and rendered output")
expect(session.current_title).to_equal("SimpleScriptTitle")
expect(session.current_body_html).to_equal("simple-script-mutated-body")
assert_contains(session.render_html_document(), "simple-script-mutated-body")
# The only admissible warning is the runtime's native-globals
# diagnostic line; any script error would appear here.
for warning in session.warnings:
    assert_contains(warning, "browser native globals")
```

</details>

#### records inline wasm as validated-but-not-executed while later JS still runs

- records inline wasm as validated-but-not-executed while later JS still runs
- load a page with an inline application/wasm module between JS tags
- assert the explicit wasm validation record
   - Expected: session.wasm_modules.len() equals `1`
   - Expected: session.wasm_modules[0].status equals `validated`
   - Expected: session.wasm_modules[0].byte_length equals `8`
- assert JS around the wasm tag executed


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("records inline wasm as validated-but-not-executed while later JS still runs")
"""The engine cannot execute wasm bytecode; it must say so explicitly:
the module is recorded with status 'validated' (never silently run,
never silently dropped), and JavaScript around it keeps executing."""
step("load a page with an inline application/wasm module between JS tags")
var session = BrowserSession.new()
val html = "<html><body>" +
    "<script>var before = 'js-before';</script>" +
    "<script type='application/wasm'>0061736d01000000</script>" +
    "<script>var after = before + ':js-after';</script>" +
    "</body></html>"
match session.open_html("https://example.test/wasm-exec.html", html):
    Ok(_): pass_do_nothing
    Err(err): fail("expected wasm page to load: {err}")

step("assert the explicit wasm validation record")
expect(session.wasm_modules.len()).to_equal(1)
expect(session.wasm_modules[0].status).to_equal("validated")
expect(session.wasm_modules[0].byte_length).to_equal(8)
assert_true(session.wasm_modules[0].valid)

step("assert JS around the wasm tag executed")
match session.eval_script("after"):
    Ok(value):
        match value:
            JsValue.String(s): expect(s).to_equal("js-before:js-after")
            _: fail("expected string result from JS after wasm")
    Err(err): fail("expected JS after wasm to evaluate: {err}")
```

</details>

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

- `REQ-SSPEC-UNIT`
- `REQ-WEB-BROWSER-003`
- `REQ-WEB-BROWSER-005`
- `REQ-SSPEC-BROWSER_ENGINE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `26a981e87a7ce59e8fd835f2e25197b7881bae3ad1b73fe7764480590711164e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `26a981e87a7ce59e8fd835f2e25197b7881bae3ad1b73fe7764480590711164e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `26a981e87a7ce59e8fd835f2e25197b7881bae3ad1b73fe7764480590711164e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/browser_engine/browser_script_execution_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/browser_script_execution_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/browser_engine/browser_script_execution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/browser_script_execution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/browser_script_execution_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/browser_script_execution_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/browser_engine/browser_script_execution_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reflects a JavaScript DOM text and title mutation in the rendered document' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/browser_script_execution_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reflects a JavaScript inline style mutation in the rendered document' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/browser_script_execution_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reflects a Simple script title and body mutation in the rendered document' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
