# BUG: boot_tcp_read_text single non-blocking read drops later TCP segments (rv64 DB SELECT fails)

**Status:** open — now the sole blocker for the rv64 DB gate (was masked by the text.len() miscompile until that was fixed)
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
