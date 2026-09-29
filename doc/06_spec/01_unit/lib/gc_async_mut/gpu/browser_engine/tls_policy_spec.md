# Tls Policy Specification

> Tests covering Browser TLS negotiated protocol policy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tls Policy Specification

## Scenarios

### Browser TLS negotiated protocol policy

#### releases runtime-owned TLS read and protocol strings

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- releases runtime-owned TLS read and protocol strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("releases runtime-owned TLS read and protocol strings")
val h1 = rt_file_read_text(
    "src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl"
) ?? ""
val tls = rt_file_read_text(
    "src/lib/gc_async_mut/gpu/browser_engine/net/tls.spl"
) ?? ""
val dns = rt_file_read_text(
    "src/lib/gc_async_mut/gpu/browser_engine/net/dns.spl"
) ?? ""
expect(h1).to_contain("val _ = browser_runtime_string_free(chunk)")
expect(h1).to_contain("self.tls.handshake_address(")
expect(tls).to_contain("val _ = browser_runtime_string_free(negotiated)")
expect(dns).to_contain("val _ = browser_runtime_string_free(raw_system_addrs)")
```

</details>

#### accepts supported versions and rejects downgrade or missing protocol

- accepts supported versions and rejects downgrade or missing protocol
   - Expected: validated_negotiated_tls_version("TLSv1.3", TlsVersion.Tls13).is_ok() is true
   - Expected: validated_negotiated_tls_version("TLSv1.2", TlsVersion.Tls12).is_ok() is true
   - Expected: validated_negotiated_tls_version("TLSv1.2", TlsVersion.Tls13).is_err() is true
   - Expected: validated_negotiated_tls_version("", TlsVersion.Tls12).is_err() is true
   - Expected: validated_negotiated_tls_version("SSLv3", TlsVersion.Tls12).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts supported versions and rejects downgrade or missing protocol")
expect(validated_negotiated_tls_version("TLSv1.3", TlsVersion.Tls13).is_ok()).to_equal(true)
expect(validated_negotiated_tls_version("TLSv1.2", TlsVersion.Tls12).is_ok()).to_equal(true)
expect(validated_negotiated_tls_version("TLSv1.2", TlsVersion.Tls13).is_err()).to_equal(true)
expect(validated_negotiated_tls_version("", TlsVersion.Tls12).is_err()).to_equal(true)
expect(validated_negotiated_tls_version("SSLv3", TlsVersion.Tls12).is_err()).to_equal(true)
```

</details>

#### rejects an HTTPS redirect to plaintext before transport

- rejects an HTTPS redirect to plaintext before transport


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an HTTPS redirect to plaintext before transport")
var registry = MockResponseRegistry.create()
registry.register_with_headers(
    "https://secure.test/start",
    302,
    [Pair("Location", "http://secure.test/plain")],
    ""
)
registry.register("http://secure.test/plain", 200, "downgraded")
set_mock_registry(registry)
val logger = Logger.new("tls-policy", BrowserLogLevel.Error)
var fetch = FetchEngine.new_for_origin(logger, "https://secure.test")
val request = FetchRequest(
    url: Url.parse_or_opaque("https://secure.test/start"),
    method: "GET",
    headers: "",
    body: [],
    mode: RequestMode.SameOrigin,
    credentials: "omit"
)

expect(fetch.fetch(request).is_err()).to_be(true)
set_mock_registry(MockResponseRegistry.create())
```

</details>

#### returns one HTTPS redirect hop unchanged for browser policy

- returns one HTTPS redirect hop unchanged for browser policy
   - Expected: result.unwrap().status equals `302`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns one HTTPS redirect hop unchanged for browser policy")
var registry = MockResponseRegistry.create()
registry.register_with_headers(
    "https://secure.test/start",
    302,
    [Pair("Location", "https://secure.test/final")],
    ""
)
registry.register("https://secure.test/final", 200, "final")
set_mock_registry(registry)
val logger = Logger.new("tls-policy", BrowserLogLevel.Error)
var fetch = FetchEngine.new_for_origin(
    logger, "https://secure.test"
)
val request = FetchRequest(
    url: Url.parse_or_opaque("https://secure.test/start"),
    method: "GET",
    headers: "",
    body: [],
    mode: RequestMode.SameOrigin,
    credentials: "omit"
)

val result = fetch.fetch_single_hop(request)
expect(result.is_ok()).to_be(true)
expect(result.unwrap().status).to_equal(302)
expect(result.unwrap().headers).to_contain(
    "Location: https://secure.test/final"
)
set_mock_registry(MockResponseRegistry.create())
```

</details>

<details>
<summary>Advanced: preserves the complete redirect method, body, and header matrix</summary>

#### preserves the complete redirect method, body, and header matrix

- preserves the complete redirect method, body, and header matrix
- Register the HTTPS redirect matrix
- Follow every HTTPS redirect case
- Verify redirected methods and bodies
   - Expected: observed.method equals `case.expected_method`
   - Expected: observed.body.len() equals `case.expected_body_len`


<details>
<summary>Executable SSpec</summary>

Runnable source: 90 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves the complete redirect method, body, and header matrix")
var registry = MockResponseRegistry.create()
val cases = [
    RedirectExpectation(301, "HEAD", "HEAD", 0, true),
    RedirectExpectation(301, "GET", "GET", 0, true),
    RedirectExpectation(301, "POST", "GET", 0, false),
    RedirectExpectation(301, "PUT", "PUT", 3, true),
    RedirectExpectation(302, "HEAD", "HEAD", 0, true),
    RedirectExpectation(302, "GET", "GET", 0, true),
    RedirectExpectation(302, "POST", "GET", 0, false),
    RedirectExpectation(302, "PUT", "PUT", 3, true),
    RedirectExpectation(303, "HEAD", "HEAD", 0, true),
    RedirectExpectation(303, "GET", "GET", 0, true),
    RedirectExpectation(303, "POST", "GET", 0, false),
    RedirectExpectation(303, "PUT", "GET", 0, false),
    RedirectExpectation(307, "HEAD", "HEAD", 0, true),
    RedirectExpectation(307, "GET", "GET", 0, true),
    RedirectExpectation(307, "POST", "POST", 3, true),
    RedirectExpectation(307, "PUT", "PUT", 3, true),
    RedirectExpectation(308, "HEAD", "HEAD", 0, true),
    RedirectExpectation(308, "GET", "GET", 0, true),
    RedirectExpectation(308, "POST", "POST", 3, true),
    RedirectExpectation(308, "PUT", "PUT", 3, true)
]

step("Register the HTTPS redirect matrix")
var index = 0
for case in cases:
    registry.register_with_headers(
        "https://secure.test/{index}-start",
        case.status,
        [Pair("Location", "https://secure.test/{index}-final")],
        ""
    )
    registry.register(
        "https://secure.test/{index}-final", 200, ""
    )
    index = index + 1
set_mock_registry(registry)
val logger = Logger.new("redirect-method-policy", BrowserLogLevel.Error)
var fetch = FetchEngine.new_for_origin(
    logger, "https://secure.test"
)
val request_headers = (
    "Content-Type: text/plain\r\n" +
    "Content-Encoding: identity\r\n" +
    "Content-Language: en\r\n" +
    "Content-Location: /source\r\n" +
    "X-Keep: yes\r\n"
)
val body_headers = [
    "Content-Type:", "Content-Encoding:",
    "Content-Language:", "Content-Location:"
]

step("Follow every HTTPS redirect case")
index = 0
for case in cases:
    val body = if case.method == "HEAD" or case.method == "GET":
        []
    else:
        [112u8, 97u8, 121u8]
    expect(fetch.fetch(FetchRequest(
        url: Url.parse_or_opaque(
            "https://secure.test/{index}-start"
        ),
        method: case.method,
        headers: request_headers,
        body: body,
        mode: RequestMode.SameOrigin,
        credentials: "omit"
    )).is_ok()).to_be(true)
    index = index + 1

step("Verify redirected methods and bodies")
index = 0
for case in cases:
    val observed = observed_mock_request(
        "https://secure.test/{index}-final"
    ).unwrap()
    expect(observed.method).to_equal(case.expected_method)
    expect(observed.body.len()).to_equal(case.expected_body_len)
    expect(observed.headers).to_contain("X-Keep: yes")
    for header in body_headers:
        expect(observed.headers.contains(header)).to_be(
            case.keep_body_headers
        )
    index = index + 1
set_mock_registry(MockResponseRegistry.create())
```

</details>


</details>

#### denies cross-origin requests labeled same-origin before transport

- denies cross-origin requests labeled same-origin before transport


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies cross-origin requests labeled same-origin before transport")
var registry = MockResponseRegistry.create()
registry.register("https://other.test/private", 200, "secret")
set_mock_registry(registry)
val logger = Logger.new("same-origin-policy", BrowserLogLevel.Error)
var fetch = FetchEngine.new_for_origin(
    logger, "https://secure.test"
)
val request = FetchRequest(
    url: Url.parse_or_opaque("https://other.test/private"),
    method: "GET",
    headers: "",
    body: [],
    mode: RequestMode.SameOrigin,
    credentials: "omit"
)

expect(fetch.fetch_single_hop(request).is_err()).to_be(true)
set_mock_registry(MockResponseRegistry.create())
```

</details>

#### does not let a no-cors cache entry bypass cors response policy

- does not let a no-cors cache entry bypass cors response policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not let a no-cors cache entry bypass cors response policy")
var registry = MockResponseRegistry.create()
registry.register("https://other.test/data", 200, "private")
set_mock_registry(registry)
val logger = Logger.new("cors-cache-policy", BrowserLogLevel.Error)
var fetch = FetchEngine.new_for_origin(
    logger, "https://secure.test"
)
val no_cors_request = FetchRequest(
    url: Url.parse_or_opaque("https://other.test/data"),
    method: "GET",
    headers: "",
    body: [],
    mode: RequestMode.NoCors,
    credentials: "omit"
)
expect(fetch.fetch_single_hop(no_cors_request).is_ok()).to_be(true)
val cors_request = FetchRequest(
    url: Url.parse_or_opaque("https://other.test/data"),
    method: "GET",
    headers: "",
    body: [],
    mode: RequestMode.Cors,
    credentials: "omit"
)

expect(fetch.fetch_single_hop(cors_request).is_err()).to_be(true)
set_mock_registry(MockResponseRegistry.create())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tls_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Browser TLS negotiated protocol policy.
- Browser TLS negotiated protocol policy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `053f19bfc85daf77a64f84bb677f894bd0451508f74f6111df97d21fc116f452`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `053f19bfc85daf77a64f84bb677f894bd0451508f74f6111df97d21fc116f452`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `053f19bfc85daf77a64f84bb677f894bd0451508f74f6111df97d21fc116f452`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/tls_policy_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tls_policy_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tls_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tls_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tls_policy_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tls_policy_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'releases runtime-owned TLS read and protocol strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tls_policy_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts supported versions and rejects downgrade or missing protocol' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tls_policy_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an HTTPS redirect to plaintext before transport' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
