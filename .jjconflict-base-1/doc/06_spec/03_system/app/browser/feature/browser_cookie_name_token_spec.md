# Cookie name token authority

Executable scenario:
`test/03_system/app/browser/feature/browser_cookie_name_token_spec.spl`

**Manual status:** complete static mirror of the executable four-step scenario.

| Requirement | Evidence |
| --- | --- |
| REQ-WEB-BROWSER-011 | The fixture is an authenticated HTTPS origin and the accepted control is `Secure`. |
| REQ-WEB-BROWSER-013 | Network and script admission reject the same non-token cookie name before it reaches authoritative state. |
| REQ-WEB-BROWSER-021 | This manual mirrors every executable step and exact terminal assertion. |

1. Open the authenticated HTTPS cookie fixture and verify its canonical origin.
2. Receive `sid=control` as a valid `Secure`, `HttpOnly`, `SameSite=None`
   control and `bad name=poison` as the malformed protected candidate; verify
   only the control is admitted and the candidate reports `invalid-name`.
3. Attempt the same malformed cookie from script; verify it reports the same
   `invalid-name` reason and cannot change the one-cookie store.
4. Observe authoritative state: script sees an empty cookie string because
   the valid control is `HttpOnly`, while the network sees exactly
   `sid=control`.

## Folded executable scenario

```simple
describe "cookie name token authority":

    it "should reject one malformed name at both cookie producer boundaries":
        step("Open the authenticated HTTPS cookie fixture")
        var cookies = CookieStore.new()
        val origin = Origin(
            scheme: "https", host: "secure.example.test", port: 443
        )
        val now = 1000
        expect(origin.to_text()).to_equal("https://secure.example.test")

        step("Receive valid and malformed protected cookies")
        val valid = parse_set_cookie(
            "sid=control; Path=/; Secure; HttpOnly; SameSite=None"
        )
        val malformed = parse_set_cookie(
            "bad name=poison; Path=/; Secure; SameSite=None"
        )
        val valid_verdict = cookies.store_from_origin(valid, origin, now)
        val network_verdict = cookies.store_from_origin(
            malformed, origin, now
        )
        expect(valid_verdict.accepted).to_be(true)
        expect(valid_verdict.reason).to_equal("ok")
        expect(network_verdict.accepted).to_be(false)
        expect(network_verdict.reason).to_equal("invalid-name")
        expect(cookies.count()).to_equal(1)

        step("Attempt the same malformed cookie from script")
        val script_verdict = cookies.store_from_script(
            malformed, origin, now
        )
        expect(script_verdict.accepted).to_be(false)
        expect(script_verdict.reason).to_equal("invalid-name")
        expect(cookies.count()).to_equal(1)

        step("Observe authoritative script and network cookie state")
        expect(cookies.script_cookie_header(origin, "/", now)).to_equal("")
        expect(cookies.get_header_for_origin(
            origin, "/", Some(origin), "GET", true, now
        )).to_equal("sid=control")
```
