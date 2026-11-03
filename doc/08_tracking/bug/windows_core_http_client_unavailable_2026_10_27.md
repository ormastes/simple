# Windows core runtime native HTTP client provider is unavailable

- Canonical ID: `windows_core_http_client_unavailable_2026_10_27`
- Status: fix-implemented-verification-pending (2026-11-03, WinHTTP provider).
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

**Revalidated 2026-11-02: still plausible because open; an active source workaround is not a compiler/provider fix; no merged fix commit with a passing regression is cited in this doc.**

## Fix 2026-11-03: WinHTTP provider

- `src/runtime/runtime_native.c`: the Windows `rt_http_perform` (`#else` branch after the POSIX socket provider) is now a WinHTTP implementation; the four `native HTTP is unavailable on Windows core runtime` returns in `rt_http_get`, `rt_http_request_with_timeout`, `rt_http_request_v2` and `rt_http_download` are removed so all four share the provider.
- Contract matches POSIX: exact binary request/response bodies, status, reason, response header block, CR/LF-bearing request headers dropped, 64 MiB response cap, 2 MiB header cap, `WINHTTP_OPTION_REDIRECT_POLICY_NEVER`, cookies/auto-auth disabled, direct connection (no implicit proxy). `https://` uses WinHTTP default certificate validation; no security flags are relaxed.
- Deadline: WinHTTP per-phase timeouts are not an overall bound (measured: 500 ms receive timeout still blocked 3 s), so a timer-queue watchdog closes the request handle at the deadline.
- Link: `winhttp` added to the seed `src/compiler_rust/common/src/platform/link_config.rs` Windows lists and to `shared_linking.spl` / `native_all_support.spl`.
- Regression: `src/runtime/test/rt_http_winhttp_loopback_selfcheck.c` (loopback Winsock server: binary GET, 302 not followed, binary POST echo, 404 text, 500 ms timeout, refused connect, bad scheme). PASS 3/3:

```
B=~/.simple/toolchains/llvm-mingw-*-ucrt-x86_64/bin
cd src/runtime && $B/x86_64-w64-mingw32-clang -O1 -I. -ffunction-sections -fdata-sections \
  test/rt_http_winhttp_loopback_selfcheck.c -o whttp.exe -Wl,--gc-sections -Wl,-Xlink=-force:unresolved \
  -lwinhttp -lws2_32 -lbcrypt -ladvapi32 -lpsapi -lole32 -lshell32 -luser32 -lsynchronization -luserenv -lntdll -ldbghelp
./whttp.exe   # rt_http_winhttp_loopback_selfcheck: PASS
```

Verification pending: DevHub HTTP text/binary/SigV4 acceptance with a redeployed Windows compiler (runtime archive rebuilt). The subprocess workaround fixture and its tags stay until that run passes.
