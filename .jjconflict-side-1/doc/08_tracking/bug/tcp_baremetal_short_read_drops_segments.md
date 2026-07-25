# BUG: boot_tcp_read_text single non-blocking read drops later TCP segments (rv64 DB SELECT fails)

**Status:** RESOLVED (2026-07-11)
**Severity:** medium-high (any HTTP body split across TCP segments is silently truncated)
**Component:** kernel networking — `src/os/kernel/boot/tcp_baremetal_min.spl::boot_tcp_read_text` (caller: `src/os/kernel/boot/http_baremetal.spl`)
**Found:** 2026-07-11 (len-fix lane; deterministic across 2 gate runs)

## Symptom

rv64 DB gate (`qemu_rv64_http_test.shs --expect-http-only --with-db`): CREATE and INSERT
now pass (`OK CREATE`/`OK INSERT`, Content-Length 9/9 correct post len-fix), but
`POST /db "SELECT codex answer"` → `ERR empty command`.

## Cause

`boot_tcp_read_text` performs a single non-blocking read loop that `break`s on the first
0-length chunk. When the request body arrives in a later TCP segment than the headers
(as the gate's SELECT consistently does), the body is dropped → the service sees an empty
command after `slice(sep+4, len)`.

## Fix direction

Read until the parsed Content-Length is satisfied (or a bounded timeout/retry on 0-length
chunks while the connection is open), not until the first empty chunk. Bound total size by
SIMPLE_DB_MAX_HTTP_BYTES.

## Related

- `doc/08_tracking/bug/llvm_native_text_len_miscompile_rv64.md` — RESOLVED; its fix
  unmasked this one (gate previously died at INSERT, never reaching SELECT).

## Resolution (2026-07-11)

`boot_tcp_read_text` no longer breaks on the first 0-length chunk: it polls
until headers complete, parses `Content-Length` once (cached), and breaks when
body bytes >= Content-Length (or immediately when there is no body), bounded
at 20000 zero-read spins. Implementation deliberately avoids rv64-hazardous
primitives (`text.len()` on TCP-derived text, optional-`?` chains) — byte
counts derive from chunk lengths.

Verified on a fresh rv64 ELF (nm-checked to contain the fix before gating):
`qemu_rv64_http_test.shs --expect-http-only --with-db` → 5 passed / 0 failed,
`DB CREATE/INSERT/SELECT... PASS (codex-41)`. This closes the rv64 DB-server
gate end-to-end (the earlier text.len() miscompile fix unmasked this bug).

Build note discovered en route: in this virtual workspace
`cargo build -p simple-driver -p simple-native-all --features llvm` does NOT
activate llvm — use `--features simple-driver/llvm,simple-native-all/llvm`.
