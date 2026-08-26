# HTTPS 303 HEAD redirect semantics

Executable scenario:
`test/03_system/app/browser/feature/browser_https_303_head_redirect_spec.spl`

**Manual status:** complete static mirror of the executable four-step scenario.

| Requirement | Evidence |
| --- | --- |
| REQ-WEB-BROWSER-010 | A same-origin `303` resolves `/final` against the original canonical HTTPS URL. |
| REQ-WEB-BROWSER-011 | The redirected request remains HTTPS and preserves metadata-only `HEAD` semantics. |

1. Queue an HTTPS `HEAD` navigation with no request body.
2. Commit a same-origin `303 See Other` response with `Location: /final`.
3. Take the single redirected request and verify its canonical HTTPS URL.
4. Verify the redirect preserved `HEAD` and an empty body instead of issuing
   `GET`.

## Folded executable scenario

```simple
describe "HTTPS 303 HEAD redirect semantics":
    it "should preserve HEAD without a body across a same-origin HTTPS 303":
        step("Queue an HTTPS HEAD navigation")
        var session = BrowserSession.new()
        expect(session.begin_network_navigation(
            "https://secure.test/start", "HEAD", "", "", ""
        ).is_ok()).to_be(true)

        step("Return a same-origin HTTPS 303")
        val initial = session.take_pending_request().unwrap()
        expect(initial.method).to_equal("HEAD")
        expect(session.commit_network_response(BrowserResponse.create(
            initial.id, "document", initial.url, 303,
            "Location: /final\n", "", ""
        )).is_ok()).to_be(true)

        step("Take the redirected request")
        val redirected = session.take_pending_request().unwrap()
        expect(redirected.url).to_equal("https://secure.test/final")

        step("Preserve HEAD redirect semantics")
        expect(redirected.method).to_equal("HEAD")
        expect(redirected.body).to_equal("")
```
