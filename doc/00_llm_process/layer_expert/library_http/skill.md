# HTTP library layer maintenance

The async HTTP client public url_encode wrapper delegates to its own family's canonical std.nogc_async_mut.http.url.url_encode. Preserve UTF-8 byte percent encoding, unreserved ASCII and the component wrapper. Do not duplicate codepoint traversal or unsupported radix to_string calls in client types.

Regression: test/fixtures/devhub/async_http_url_encode/main.spl. Native Phase2 fixture evidence passed; this does not qualify a full DevHub build. See doc/09_report/verification/devhub_native_build_20261030.md for remaining generic/compiler and database blockers.
