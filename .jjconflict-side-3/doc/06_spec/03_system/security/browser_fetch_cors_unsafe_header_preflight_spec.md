# Browser Fetch CORS Unsafe-Header Preflight

> Proves a non-safelisted cross-origin request header is authorized through the
> real OPTIONS path before any actual request can reach the endpoint.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

## Scenario

### should deny an ungranted custom header before the actual request

1. Register a cross-origin endpoint that omits X-Admin-Action permission.
2. Issue a credential-free CORS GET carrying X-Admin-Action.
3. Observe the first and only OPTIONS advertising x-admin-action.
   - The first request method is `OPTIONS`.
   - `Access-Control-Request-Headers` contains `x-admin-action`.
   - Exactly one request is observed and the `GET` count is zero.
4. Reject the fetch before the ungranted action reaches the endpoint.
   - Fetch returns `CORS preflight denied`.

<details>
<summary>Executable SSpec</summary>

```simple
step("Register a cross-origin endpoint that omits X-Admin-Action permission")
var registry = MockResponseRegistry.create()
registry.register_with_headers(
    "https://api.test/admin",
    204,
    [Pair("Access-Control-Allow-Origin", "https://app.test")],
    ""
)
set_mock_registry(registry)

step("Issue a credential-free CORS GET carrying X-Admin-Action")
var fetch = FetchEngine.new_for_origin(
    Logger.new("cors-header-preflight", BrowserLogLevel.Error),
    "https://app.test"
)
val result = fetch.fetch(FetchRequest(
    url: Url.parse_or_opaque("https://api.test/admin"),
    method: "GET",
    headers: "X-Admin-Action: delete\r\n",
    body: [],
    mode: RequestMode.Cors,
    credentials: "omit"
))

step("Observe the first and only OPTIONS advertising x-admin-action")
match observed_mock_request("https://api.test/admin"):
    Some(observed):
        expect(observed.method).to_equal("OPTIONS")
        expect(observed.headers).to_contain(
            "Access-Control-Request-Headers: x-admin-action"
        )
    nil:
        fail("missing CORS preflight request")
expect(observed_mock_request_count(
    "https://api.test/admin"
)).to_equal(1)
expect(observed_mock_request_count(
    "https://api.test/admin", "GET"
)).to_equal(0)

step("Reject the fetch before the ungranted action reaches the endpoint")
match result:
    Err(error):
        expect(error.message).to_contain("CORS preflight denied")
    Ok(_):
        fail("ungranted custom-header request reached the endpoint")
set_mock_registry(MockResponseRegistry.create())
```

</details>

## Traceability

| Requirement | Evidence |
|---|---|
| REQ-WEB-BROWSER-010 | Real Fetch OPTIONS request carries exact ACRH and no actual GET follows denial |
| REQ-WEB-BROWSER-012 | Missing custom-header permission fails closed before endpoint side effects |
| REQ-WEB-BROWSER-021 | Modern four-step executable SSpec and mirrored manual |

Runtime execution remains pending; this manual records no SPipe PASS.
