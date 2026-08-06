# decode_chunked treats a malformed chunk size as end-of-body (silent truncation)

- **Status:** OPEN
- **Found:** 2026-08-06
- **Area:** `src/lib/nogc_sync_mut/http/headers.spl` (+ gc_async_mut / nogc_async_mut copies)
- **Severity:** high — reachable on an HTTP server request path with attacker-controlled input

## Symptom

`decode_chunked` returns a silently truncated (usually empty) body, with no
error, for a chunked message whose framing is invalid.

Probe (seed interpreter, rc=0 — no error raised):

```
decode_chunked("XYZ\r\nhello\r\n0\r\n\r\n")  -> ""      # non-hex chunk size
decode_chunked("FF\r\nhello\r\n0\r\n\r\n")   -> ""      # size 255, only 5 octets present
decode_chunked("5\r\nhello\r\n0\r\n\r\n")    -> "hello" # well-formed control
```

## Root cause

`headers.spl` `decode_chunked`:

- `parse_hex_text(size_str)` maps any non-HEXDIG character to `0` (via
  `hex_to_int`'s catch-all `return 0`). A chunk size of `0` is the RFC 7230
  §4.1 last-chunk terminator, so a **malformed** size is indistinguishable from
  a **legitimate end of body** and hits `if chunk_size == 0: break`.
- `if data_end > encoded.length(): break` — a chunk that declares more octets
  than are present also exits normally, returning the partial accumulation.

Both failure paths `break` out of the loop and `return parts.join("")`. The
function's return type is `text`, so it has no channel to report a framing
error, and every caller reads the result as a successful decode.

## Oracle (external)

RFC 7230 §4.1: `chunk-size = 1*HEXDIG` — a non-HEXDIG chunk size is not a
zero-length chunk, it is a syntax error. RFC 7230 §3.4: a server that receives
an incomplete request message MUST respond with 400 (Bad Request). Silently
substituting an empty body is neither.

## Blast radius — REACHABLE

- `src/lib/nogc_async_mut/http_server/parser.spl:132` — `self.body =
  decode_chunked(raw)` on the live request-parsing path. A request with an
  invalid chunk size is accepted as a request with an empty body instead of
  being rejected, which is request-smuggling-adjacent: the server's view of
  where the body ends can diverge from an upstream proxy's.
- `src/lib/nogc_sync_mut/http/http1.spl:214` — `decode_chunked_with_trailers`.
- The gc_async_mut and nogc_async_mut copies of `headers.spl` carry the same code.

Note this became reachable only once `hex_to_int` was repaired (see
`7a1e3a5e777`); before that every call raised `Function 'str.char_code' not
found`, so the truncation path could not execute.

## Why not fixed inline

The fix requires an API contract decision that spans a module boundary:
`decode_chunked -> text` cannot signal failure, so repairing it means either
changing the signature to a `Result`/tuple across all three tiers, or adding a
sentinel that `http_server/parser.spl` maps to a 400 response. Both change the
caller contract on a server path and warrant their own change with its own
RED/GREEN/SABOTAGE cycle rather than being folded into the `hex_to_int` fix.

## Suggested fix

Distinguish "parsed 0" from "not a valid hex size": have the chunk-size parse
report validity (e.g. return `-1` for a size line containing a non-HEXDIG, and
for a chunk whose data runs past the buffer), and have `decode_chunked` surface
that to callers so `http_server/parser.spl` can answer 400 instead of accepting
an empty body.
