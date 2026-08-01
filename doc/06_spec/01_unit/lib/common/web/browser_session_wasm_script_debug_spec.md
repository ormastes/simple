# Browser Session Wasm Script Debug Specification

> <details>

<!-- sdn-diagram:id=browser_session_wasm_script_debug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_wasm_script_debug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_wasm_script_debug_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_wasm_script_debug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Wasm Script Debug Specification

## Scenarios

### BrowserSession WASM script debug

#### debug inline

- var session = BrowserSession new
- Ok
- print "inline modules={session wasm modules len
- print "inline record={session wasm modules[0] summary
- Ok
- print "inline js={ display js debug
- Err
   - Expected: session.wasm_modules.len() equals `1`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body><script>var before = 'js-before';</script><script type='application/wasm'>0061736d01000000</script><script>var after = before + ':js-after';</script></body></html>"
val result = session.open_html("https://example.com/inline-wasm.html", html)
match result:
    Ok(_):
        print "inline modules={session.wasm_modules.len()} warnings={session.warnings.len()}"
        if session.wasm_modules.len() > 0:
            print "inline record={session.wasm_modules[0].summary()} valid={session.wasm_modules[0].valid.to_text()}"
        val js_result = session.eval_script("after + ':' + typeof WebAssembly.instantiate")
        match js_result:
            Ok(value):
                print "inline js={_display_js_debug(value)}"
            Err(err):
                print "inline js err={err}"
        expect(session.wasm_modules.len()).to_equal(1)
    Err(err):
        fail("load err {err}")
```

</details>

#### debug external

- var session = BrowserSession new
- Ok
- Some
- Ok
- print "external modules={session wasm modules len
- Ok
- print "external js={ display js debug
- Err
- Err
   - Expected: session.wasm_modules.len() equals `1`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body><script>var order = 'before';</script><script type='application/wasm' src='/app.wasm'></script><script>order = order + ':after';</script></body></html>"
val result = session.open_html("https://example.com/wasm-page.html", html)
match result:
    Ok(_):
        match session.take_pending_request():
            Some(request):
                print "external request={request.kind}:{request.url}:{request.content_type}"
                val committed = session.commit_network_response(BrowserResponse.create(request_id: request.id, kind: "wasm", url: request.url, status: 200, headers: "Content-Type: application/wasm\n", body: "0061736d01000000", error: ""))
                match committed:
                    Ok(_):
                        print "external modules={session.wasm_modules.len()} warnings={session.warnings.len()}"
                        val js_result = session.eval_script("order")
                        match js_result:
                            Ok(value):
                                print "external js={_display_js_debug(value)}"
                            Err(err):
                                print "external js err={err}"
                    Err(err):
                        print "external commit err={err}"
            nil:
                print "external no request"
        expect(session.wasm_modules.len()).to_equal(1)
    Err(err):
        fail("load err {err}")
```

</details>

#### debug invalid

- var session = BrowserSession new
- Ok
- print "invalid modules={session wasm modules len
- print "invalid record={session wasm modules[0] summary
- Ok
- print "invalid js={ display js debug
- Err
   - Expected: session.wasm_modules.len() equals `1`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val html = "<html><body><script>var marker = 'before';</script><script type='application/wasm'>0061736d00000000</script><script>marker = marker + ':after';</script></body></html>"
val result = session.open_html("https://example.com/invalid-wasm.html", html)
match result:
    Ok(_):
        print "invalid modules={session.wasm_modules.len()} warnings={session.warnings.len()}"
        if session.wasm_modules.len() > 0:
            print "invalid record={session.wasm_modules[0].summary()} valid={session.wasm_modules[0].valid.to_text()}"
        val js_result = session.eval_script("marker")
        match js_result:
            Ok(value):
                print "invalid js={_display_js_debug(value)}"
            Err(err):
                print "invalid js err={err}"
        expect(session.wasm_modules.len()).to_equal(1)
    Err(err):
        fail("load err {err}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_wasm_script_debug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession WASM script debug

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
