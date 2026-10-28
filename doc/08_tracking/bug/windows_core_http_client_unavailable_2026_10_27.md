# Windows core runtime native HTTP client provider is unavailable

- Canonical ID: `windows_core_http_client_unavailable_2026_10_27`
- Status: open; an active source workaround is not a compiler/provider fix.
- Owner: DevHub completion / compiler-runtime owners.
- Created: 2026-10-27.
- Producer: existing P2 `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`; no compiler rebuild.
- Source: `src/runtime/runtime_native.c`.
- Regression: `test/fixtures/devhub/native_http_curl/main.spl`.

The Windows core native HTTP branch explicitly returns unavailable. A shared real curl compatibility transport uses bounded execution, private mode384 header/body/response files, no redirects and no TLS bypass; request secrets are absent from argv. Applications retain configured public std interfaces.

## Evidence

Source-confirmed Windows provider gap. Actual curl8.21.0 exists on the qualification host. HTTP text and signed binary loopback acceptance remains separately bound to the parent qualification artifacts; source review alone is not runtime PASS.

## Removal condition

Retire only after the selected Windows native provider supports text and exact binary bodies, status and errors, size and time bounds, redirects/TLS policy, secret handling and independent HTTP/SigV4 acceptance with the deployed compiler. An installed curl workaround does not close the missing provider bug.

The standard SSpec suite, all runtime-family combinations and any claim not explicitly tied to an actual artifact remain unqualified. Record the workaround commit in the canonical BugDatabase investigation log after integration; never retire it from a source-only review.
