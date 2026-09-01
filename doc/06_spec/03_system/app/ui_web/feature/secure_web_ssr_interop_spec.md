# Secure web SSR interoperability

**Status:** PARTIAL/RED — executable scenarios prove representative HTML lowers
to a non-empty Draw IR v2 composition, produces a 96x64 CPU Engine2D readback
with painted pixels, and reaches the hosted SSR request adapter as a valid
96x64 PNG response. A socket-neutral BrowserHttpTransport scenario also proves
that the canonical H1 client preserves POST method, headers, and body before
the captured payload enters the real hosted SSR adapter and produces a 200
PNG response. Invalid method, empty body, and bounded-size failures are also
asserted before rendering. Live HTTPS, independent browser
interoperability, asynchronous completion/non-blocking behavior, and
resource-counter oracles remain unresolved and retain fail-fast placeholders.

The currently executable render flow invokes the browser transport adapter,
canonical H1 request capture seam, semantic evidence adapter, and hosted
in-memory request adapter. The H1 registry's 202 response is only a deterministic
fixture acknowledgement; the independently asserted 200/PNG result comes from
`render_ssr_request`. This does **not** prove a bound socket,
HTTP Worker dispatch, TLS 1.3, independent browser interoperability, scheduler
pool admission, or unrelated-client progress. Those broader scenarios remain
deliberately fail-fast. The accepted render path is web semantic/layout ->
`DrawIrComposition` -> Engine2D -> PNG, with semantic composition properties,
painted readback, PNG signature, and encoded dimensions checked independently.

## Executable scenarios

- Representative HTML produces Draw IR v2 batches, commands, and painted CPU
  readback pixels.
- BrowserHttpTransport preserves the SSR POST method, content headers, and exact
  body bytes; the captured request then produces a real hosted 200 PNG result.
- Hosted `render_ssr_request` returns `image/png` with an exact 96x64 IHDR.
- GET, empty POST, and oversized POST inputs return 405, 400, and 413 without
  PNG bytes.

## Unresolved release evidence

- Live TLS 1.3 HTTP exchange through the production Worker.
- Simple Browser, Chromium, Firefox, and OpenSSL interoperability.
- Auth, downgrade, replay, overload, timeout, and disconnect transcripts.
- Runtime-pool admission plus progress of an unrelated client.
- Accept, cancellation, render, and send resource counters.

**Screenshots:** none retained; live browser/HTTPS capture remains unresolved.

**Executable SPipe:** `test/03_system/app/ui_web/feature/secure_web_ssr_interop_spec.spl`
