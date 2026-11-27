# Read-only native gateway service v1

Source: `test/01_unit/app/scv/gateway_service_v1_spec.spl`.

This is an authored source-ready manual, not generated execution evidence.
Phase 3 runtime admission, SSpec execution, docgen and manual quality scan are
deferred. No scenario below is marked passing. Fixtures replace the GitHub
provider and open no listener; they prove neither live GitHub reads nor TLS.

| Scenario | Action | Required observation |
|---|---|---|
| Exact configuration | Parse a strict native SDN mapping, then try wildcard listener, extra/duplicate fields and foreign host | Only the exact loopback repository mapping is admitted |
| Secret references | Check environment identifier and bearer lexical bounds | Header injection, empty/short tokens and command-like environment names are refused |
| Capabilities authentication | Send an authenticated capability request, duplicate bearer headers, then a malformed unauthenticated body | Authenticated response validates under the bound request; both unauthenticated forms return HTTP 401 without echoing the body |
| Native reads | Inject typed ref, commit and binary blob results | Every envelope binds the request and repository, carries `not_publication`, and blob bytes remain `00ff0a` |
| Transport request rejection | Supply duplicate media headers, query arguments, GET or an oversized body | Native dispatch refuses the request before provider use |
| Forged successes | Alter numeric repository, verification enum, blob bytes, selector, request count, tree or parents | Service returns `gateway_provider_result_rejected` with no payload or integrity claim |
| Scope and write denial | Try another logical repository, publication method and invalid ref path | Denial occurs before the injected provider can return a read |
| Upstream redaction | Return secret-bearing provider error text | Native failure contains only `gateway_upstream_read_failed` and validates under the request |
| Transport admission | Inspect the fixed server policy and request startup without development authority | Body/header/connection/time/response limits match the contract; production startup and arbitrary CLI arguments are refused |
| Native client CLI | Try a write method, missing or unexpected selector and duplicate option | Arguments are refused before runtime HTTP or credential access |

After runtime admission, generate this manual through the canonical docgen
owner and review its actual output. Localhost HTTP execution and live GitHub
route qualification are separate required follow-ups; neither is inferred from
these injected assertions.
