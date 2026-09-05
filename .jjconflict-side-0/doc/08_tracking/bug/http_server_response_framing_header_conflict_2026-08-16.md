# HTTP server response framing header conflict

**Status:** FIX PREPARED; ADMITTED STAGE-4 EXECUTION BLOCKED (2026-08-16)

## Failure

`_serialize_response_head` emitted canonical `Content-Length` and
`Connection: close`, then appended every application header. A handler could
therefore add a second mixed-case `Content-Length`, `Transfer-Encoding`, or
`Connection` field, or inject a new field through CR/LF in a name or value.

## Owner and repair

The synchronous writer in
`src/lib/nogc_sync_mut/http_server/response.spl` is the sole response-framing
owner. It now suppresses application framing fields case-insensitively and
drops non-token field names and control-bearing values. The AC-2 system spec
checks one correct length, no transfer coding, forced close, rejected injection,
and a complete body through both serialization and a real loopback connection.

## Remaining evidence

Run the focused web spec, `sspec-maintain scan`, and `spipe-docgen` exactly once
with the admitted Stage-4 CLI recorded by the secure-server test plan. Rust
seed and Stage-2/3 output cannot close this record.
