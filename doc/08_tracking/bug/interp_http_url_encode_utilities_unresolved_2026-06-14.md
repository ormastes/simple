# interp: url_encode unusable in interpreter — "Cannot resolve module: utilities"

- ID: interp_http_url_encode_utilities_unresolved_2026-06-14
- Severity: P2
- Area: interpreter / module resolution
- Found: 2026-06-14 (writing test/01_unit/app/itf/adapter_outlook_curl_spec.spl)

## Symptom

Any code path that calls `url_encode` fails to execute under `bin/simple run`
and the unit test runner (interpreter), even though the function compiles and
runs natively. The module load emits:

```
[WARN] Failed to load export source error=semantic: Cannot resolve module: utilities
```

and the calling function silently dies (no result returned). A probe that
prints `CLIENT_OK`, then calls `outlook_curl_folder_list_url` (which calls
`url_encode`), stops after `CLIENT_OK` with no URL output.

## Reproduce

```
cat > /tmp/ue.spl <<'EOF'
use std.nogc_sync_mut.http_client.types.{url_encode}
fn main():
    print("START")
    print("ENC=" + url_encode("ops@acme.com"))
main()
EOF
SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed \
  bin/simple run /tmp/ue.spl
# prints START, never prints ENC=
```

## Dependency chain

`std.nogc_sync_mut.http_client.types` (re-exports `url_encode`)
-> `nogc_sync_mut.http.url` -> `std.nogc_sync_mut.http.common` -> ... -> a bare
`utilities` module the interpreter cannot resolve. Natively / in compiled mode
the chain resolves; only the interpreter's module resolver fails.

## Impact

- URL-builder unit coverage for `adapter_outlook_curl.spl`
  (`outlook_curl_folder_list_url`, `outlook_curl_messages_url`) cannot be
  exercised in the interpreter test runner. Those it-blocks were omitted from
  `test/01_unit/app/itf/adapter_outlook_curl_spec.spl`; the remaining 12 blocks
  (client construction, token cache, argv builders, status/error mapping,
  status-tail parsing, response splitting) execute and pass.
- The sibling `adapter_bitbucket_curl_spec.spl` is unaffected because its URL
  builders are plain string concatenation and never call `url_encode`.

## Fix options (unverified hypotheses)

1. Make the interpreter module resolver resolve the `utilities` module the same
   way the native frontend does (path/alias mismatch most likely).
2. Drop the deep `utilities` dependency from the `http.url`/`http.common` chain
   so `url_encode` has no unresolvable transitive import.

## Triage 2026-09-13 — LEFT OPEN (reported error gone, a worse failure took its place)

- **measured** (Rust seed `bin/simple` v1.0.0-rc.1, Windows): the reported `Cannot resolve module: utilities` warning no longer appears. But the repro still fails, now harder: `use std.nogc_sync_mut.http_client.types.{url_encode}` prints `START` and then **SIGSEGVs** (exit 139) at the call, with no diagnostic.
- **measured**: `url_encode` does not exist in `src/lib/nogc_sync_mut/http_client/types.spl` at all — that file defines `url_encode_component` (`:44`). Importing the nonexistent name is accepted silently and only crashes at the call. `url_encode_component` from the same module SIGSEGVs identically, so the crash is the module, not the missing name.
- **measured**: the `gc_async_mut` twin works — `use std.gc_async_mut.http_client.types.{url_encode}` prints `ENC=ops%64acme.com`, exit 0.
- **measured**, adjacent defect found while verifying and NOT fixed here: that output is wrong. `@` is 0x40, so the correct encoding is `%40`. The cause is that `i64.to_string(radix)` ignores its radix — `val c = 64; c.to_string(16)` and `c.to_string(2)` both print `64`. Five stdlib percent-encoders depend on it (`gc_async_mut/http_client/types.spl:55`, `gc_async_mut/oauth2.spl:230`, `nogc_async_mut/http_client/types.spl:55`, `nogc_async_mut/oauth2.spl:230`, `nogc_sync_mut/oauth2.spl:230`), so every one of them emits decimal where hex is required. Deliberately not patched at the call sites: that would mask a broken primitive across the whole stdlib. Fix belongs in `to_string(radix)`.
- Verdict: OPEN — the module-resolution half is fixed; a segfault and a wrong-output primitive remain.
