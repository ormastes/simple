# GAP-TLS-3: Accepted TcpStream has no encrypted Pure-Simple overlay

## Triage 2026-09-13 — STILL OPEN: capability gap, nothing to close
- **measured** — `src/lib/nogc_sync_mut/http_server/tls_server.spl` still exists and is
  still the only TLS surface in that directory (no `tls_stream.spl`, no handshake or
  key-schedule module alongside it).
- **inferred** — this entry has an explicit unblock condition (a live handshake plus RFC
  known-answer evidence) and describes a thing to build, not behaviour that can stop
  reproducing. No such evidence exists in the tree. Not closable by triage.

Status: closed (2026-09-13 triage) — see the "Closed 2026-09-13" section below
Status re-verified 2026-08-17 by source inspection (triage shard 01).
Owner: Pure-Simple TLS transport lane

`src/lib/nogc_sync_mut/http_server/tls_server.spl` receives a `TcpStream`, but
there is no owned encrypted stream that frames TLS records, authenticates and
decrypts reads, encrypts writes, and preserves timeout/close behavior. The
secure server now fails closed instead of passing cleartext through.

Unblock when an owned `TlsStream`-equivalent over the existing TCP facade is
implemented and a live production-listener scenario proves encrypted request
and response bytes, invalid-record rejection, timeout handling, and clean close.

## Ground truth 2026-11-13 (lane http-20261113, tree at 6a5f8e708f2)

The owned encrypted-stream overlay this record called missing is now VERIFIED
PRESENT:

- `src/lib/nogc_async_mut/io/tls.spl`: `class AsyncTlsStream` and
  `class AsyncTlsListener` with `accept() -> Result<AsyncTlsStream, IoError>` —
  an owned TLS stream/listener pair over the TCP facade (TLS 1.2 path).
- `src/lib/common/net/tls_application_record_stream_v1.spl`:
  `class TlsApplicationRecordStreamV1` + `tls_application_record_stream_new_v1`
  (record-layer ingest/deframing with sequence/overflow/malformed states,
  unit-oracled by `test/01_unit/lib/common/net/tls_application_record_stream_spec.spl`).
- `src/lib/nogc_sync_mut/http_server/tls_server.spl`: `TlsServerConn` wraps a
  `TcpStream`; `tls_server_accept` never falls through to plaintext.

STILL OPEN under this record's own unblock condition: no live
production-listener scenario proves encrypted request/response bytes,
invalid-record rejection, timeout handling, and clean close — no live TLS
listener spec exists under `test/02_integration` or `test/03_system` (only
fail-closed policy and record-unit specs; the secure web server system spec
uses `TcpStream.from_accepted_fd(-1)`). The literal 2026-09-13 observation
("no tls_stream.spl alongside tls_server.spl") still holds for that directory,
but the capability now exists in the tree. DB must stay OPEN pending the
live-scenario evidence.

## Triage note 2026-11-25 (p2w2-aj) — header correction

**Disposition: STILL OPEN — SKIP for this lane.** The line-11 header
"Status: closed (2026-09-13 triage)" is **misleading** and should read OPEN:
the 2026-11-13 ground-truth section above already corrected it — the owned
encrypted-stream capability is present in the tree
(`src/lib/nogc_async_mut/io/tls.spl` `AsyncTlsStream`/`AsyncTlsListener`,
`tls_application_record_stream_v1.spl`, `TlsServerConn` in
`tls_server.spl` — all re-confirmed present on release/1.0.0 HEAD), but the
record's own unblock condition (a live production-listener scenario proving
encrypted request/response bytes, invalid-record rejection, timeout, clean
close) is still unmet: the only spec touching `tls_server_accept`,
`test/03_system/web/server/secure_pure_simple_web_server_spec.spl`, still
uses `TcpStream.from_accepted_fd(-1)` stubs (lines 191/204/209/214/219), not
a live listener. Building that live-scenario evidence is a feature-sized lane
(live TLS handshake + RFC known-answer vectors) and cannot run on this
seed-only Windows host — `bin/simple.exe test` fails repo-wide at HEAD with
`unknown decorator '@representation_boundary'`. Verified by code inspection;
remains OPEN pending the live-scenario spec.
