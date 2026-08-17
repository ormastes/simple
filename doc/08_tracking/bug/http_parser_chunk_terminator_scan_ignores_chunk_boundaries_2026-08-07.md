# HTTP request parser scans for the chunked terminator without respecting chunk boundaries

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Found:** 2026-08-07
- **Area:** `src/lib/nogc_async_mut/http_server/parser.spl` (`ParseState.Body`, chunked branch)
- **Severity:** medium — a legal request is rejected with 400; before 2026-08-07 the
  same input was silently mis-framed, which was worse

## Symptom

`parser.spl` decides where a chunked body ends with a flat substring search:

```
val term = self.buffer.index_of("0\r\n\r\n")
val raw = self.buffer.slice(0, term + 5)
```

The scan is not boundary-aware — it matches the byte sequence `0\r\n\r\n`
**anywhere**, including inside chunk-data, where those octets are ordinary
payload rather than the last-chunk. A legal request whose chunk-data happens to
contain that sequence has `raw` cut short at the wrong offset.

Probe (seed interpreter), `POST` + `Transfer-Encoding: chunked`, body
`9\r\nab0\r\n\r\ncd\r\n0\r\n\r\n` — one well-formed 9-octet chunk whose data is
`ab0\r\n\r\ncd`:

```
before 2026-08-07:  T_embedded => Ok body=[]     # accepted, body silently wrong
after  2026-08-07:  T_embedded => Err msg=[chunked framing error: chunk data runs past end of body]
```

## Oracle

RFC 7230 §4.1: `chunked-body = *chunk last-chunk trailer-part CRLF`, where
`chunk = chunk-size [ chunk-ext ] CRLF chunk-data CRLF`. The end of the body is
determined by **decoding chunk by chunk** — chunk-data is `1*OCTET` of length
`chunk-size` and is not scanned for delimiters. A recipient that locates the
last-chunk by substring search is not implementing §4.1.

## Relationship to the decode_chunked fix

This is a **separate** defect from
`decode_chunked_malformed_size_silently_truncates_body_2026-08-06.md`, and it
lives one layer up, in the caller. Making `decode_chunked` report framing errors
converted this case from *silent acceptance of a wrong body* (a smuggling
vector — the server's body differs from what an upstream proxy forwarded) into
a *400 on a legal request* (fail-closed, an availability bug). That is a strict
improvement but still not correct.

## Fix direction

Replace the substring scan with an incremental, boundary-aware chunk scanner
that walks size line → `chunk-size` octets → CRLF and reports "need more data"
until it reaches a genuine last-chunk. That also removes the need to buffer the
whole body before decoding. It was deliberately not folded into the
`decode_chunked` change: it rewrites the parser's streaming state machine and
needs its own RED/GREEN/SABOTAGE cycle.
