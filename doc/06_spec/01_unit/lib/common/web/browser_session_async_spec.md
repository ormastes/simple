# BrowserSession Async Fetch

The response body is an internal one-shot resource. `bodyUsed` mirrors that
internal state; assigning `false` cannot reset it. The first body reader keeps
its exact result, the next cross-reader call rejects with the stable text
`TypeError: Body is unusable`, and attached Promise reactions retain order.
An invalid first JSON decode consumes the body before rejecting, so a later
reader rejects as already consumed.

Executable specification:
`test/01_unit/lib/common/web/browser_session_async_spec.spl`

## Consume response bodies exactly once

1. Queue text, JSON, blob, array-buffer, and malformed-JSON responses.
2. Create the first reader Promise, assign `bodyUsed = false`, then create a
   different reader Promise before attaching either Promise handler.
3. Resolve the five network responses.
4. Require exact first results, authoritative `true:true` body state across the
   tamper, stable second-call rejection text, malformed-JSON first rejection,
   and first-before-second callback order.

<details>
<summary>Complete executable scenario</summary>

```simple
use std.spec.*
use std.gc_async_mut.web.browser_session.{BrowserSession, BrowserResponse}
use std.gc_async_mut.web.browser_session_loading.*
use std.gc_async_mut.web.browser_session_runtime.*
use std.js.types.js_types.{JsValue}

fn _display_js(v: JsValue) -> text:
    match v:
        JsValue.Undefined: "undefined"
        JsValue.Null: "null"
        JsValue.Boolean(b): if b: "true" else: "false"
        JsValue.Number(n):
            var s = "{n}"
            if s.ends_with(".0"):
                s = s.slice(0, s.len() - 2)
            s
        JsValue.String(s): s
        JsValue.Object(id): "[object Object]"
        JsValue.Array(id): "[object Array]"
        JsValue.Function(id): "[Function]"
        JsValue.Symbol(id): "Symbol()"

fn _commit_next_fetch(
    session: BrowserSession, expected_url: text, headers: text, body: text
):
    match session.take_pending_request():
        Some(request):
            expect(request.url).to_equal(expected_url)
            val committed = session.commit_network_response(
                BrowserResponse.create(
                    request_id: request.id,
                    kind: "fetch",
                    url: request.url,
                    status: 200,
                    headers: headers,
                    body: body,
                    error: ""
                )
            )
            match committed:
                Ok(_): expect(request.kind).to_equal("fetch")
                Err(e): fail("Expected fetch response commit to succeed: {e}")
        nil:
            fail("Expected pending fetch request for {expected_url}")

describe "BrowserSession async fetch":
    it "consumes text, JSON, blob, and array-buffer response bodies once":
        step("Queue one fetch for every response body reader")
        var session = BrowserSession.new()
        session.open_html(
            "https://example.com/app",
            """
            <html><body><script>
            var order = '';
            var textFirst = ''; var textSecond = 'pending'; var textUsed = '';
            var jsonFirst = ''; var jsonSecond = 'pending'; var jsonUsed = '';
            var blobFirst = ''; var blobSecond = 'pending'; var blobUsed = '';
            var bufferFirst = ''; var bufferSecond = 'pending'; var bufferUsed = '';
            var badJsonFirst = 'pending'; var badJsonSecond = 'pending'; var badJsonUsed = '';
            fetch('/text').then(function(r) {
                var first = r.text(); textUsed = '' + r.bodyUsed; r.bodyUsed = false; textUsed = textUsed + ':' + r.bodyUsed;
                var second = r.json();
                first.then(function(v) { textFirst = v; order = order + 'text:first>'; });
                second.then(function() { textSecond = 'fulfilled'; }, function(e) { textSecond = e; order = order + 'text:second>'; });
            });
            fetch('/json').then(function(r) {
                var first = r.json(); jsonUsed = '' + r.bodyUsed; r.bodyUsed = false; jsonUsed = jsonUsed + ':' + r.bodyUsed;
                var second = r.blob();
                first.then(function(v) { jsonFirst = '' + v; order = order + 'json:first>'; });
                second.then(function() { jsonSecond = 'fulfilled'; }, function(e) { jsonSecond = e; order = order + 'json:second>'; });
            });
            fetch('/blob').then(function(r) {
                var first = r.blob(); blobUsed = '' + r.bodyUsed; r.bodyUsed = false; blobUsed = blobUsed + ':' + r.bodyUsed;
                var second = r.arrayBuffer();
                first.then(function(v) { blobFirst = v.size + ':' + v.type; order = order + 'blob:first>'; return v.text(); }).then(function(v) { blobFirst = blobFirst + ':' + v; });
                second.then(function() { blobSecond = 'fulfilled'; }, function(e) { blobSecond = e; order = order + 'blob:second>'; });
            });
            fetch('/buffer').then(function(r) {
                var first = r.arrayBuffer(); bufferUsed = '' + r.bodyUsed; r.bodyUsed = false; bufferUsed = bufferUsed + ':' + r.bodyUsed;
                var second = r.text();
                first.then(function(v) { bufferFirst = '' + v.byteLength; order = order + 'buffer:first>'; });
                second.then(function() { bufferSecond = 'fulfilled'; }, function(e) { bufferSecond = e; order = order + 'buffer:second>'; });
            });
            fetch('/bad-json').then(function(r) {
                var first = r.json(); badJsonUsed = '' + r.bodyUsed; r.bodyUsed = false; badJsonUsed = badJsonUsed + ':' + r.bodyUsed;
                var second = r.text();
                first.then(function() { badJsonFirst = 'fulfilled'; }, function(e) { badJsonFirst = e; order = order + 'bad-json:first>'; });
                second.then(function() { badJsonSecond = 'fulfilled'; }, function(e) { badJsonSecond = e; order = order + 'bad-json:second>'; });
            });
            </script></body></html>
            """
        )

        step("Resolve each first body consumption")
        _commit_next_fetch(session, "https://example.com/text", "", "alpha")
        _commit_next_fetch(
            session, "https://example.com/json",
            "Content-Type: application/json\n", "42"
        )
        _commit_next_fetch(
            session, "https://example.com/blob",
            "Content-Type: text/plain\n", "bravo"
        )
        _commit_next_fetch(session, "https://example.com/buffer", "", "bytes")
        _commit_next_fetch(
            session, "https://example.com/bad-json",
            "Content-Type: application/json\n", "{"
        )

        step("Observe first values and second-consumption rejections")
        val result = session.eval_script(
            "textFirst + '|' + textUsed + '|' + textSecond + '|' + jsonFirst + '|' + jsonUsed + '|' + jsonSecond + '|' + blobFirst + '|' + blobUsed + '|' + blobSecond + '|' + bufferFirst + '|' + bufferUsed + '|' + bufferSecond + '|' + badJsonFirst + '|' + badJsonUsed + '|' + badJsonSecond + '|' + order"
        )
        match result:
            Ok(value):
                expect(_display_js(value)).to_equal(
                    "alpha|true:true|TypeError: Body is unusable|42|true:true|TypeError: Body is unusable|5:text/plain:bravo|true:true|TypeError: Body is unusable|5|true:true|TypeError: Body is unusable|invalid-json|true:true|TypeError: Body is unusable|text:first>text:second>json:first>json:second>blob:first>blob:second>buffer:first>buffer:second>bad-json:first>bad-json:second>"
                )
            Err(e):
                fail("Expected response body consumption state to evaluate: {e}")
```

</details>
