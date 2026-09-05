# decode_chunked treats a malformed chunk size as end-of-body (silent truncation)

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
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

## Fix (2026-08-07)

### Error channel

`decode_chunked` now returns `Result<text, text>`, and
`http1.decode_chunked_with_trailers` returns `Result<tuple, text>`. This is the
repo's existing convention for a recoverable failure, not a new one:
`validate_no_duplicate_singletons(headers: list) -> Result<list, text>` already
lives in all three `headers.spl` copies with the same `Err("...")` / trailing
`Ok(x)` shape, and `.claude/rules/language.md` mandates `Result<T, E>` for error
handling. `http_server/parser.spl` already returns
`Result<i64, HttpServerError>`, so the new `Err` maps straight onto the existing
`HttpServerError.ParseError` / `ParseState.Error` path.

A parallel `decode_chunked_checked` was deliberately NOT added — that would have
left the truncating function callable, which is the defect.

### Framing errors now reported (all were silent `break`s returning a partial body)

| Input shape | Old | New |
|---|---|---|
| size line not 1*HEXDIG (`XYZ`) | `""`, rc=0 | `Err` |
| chunk declares more octets than present (`FF`/5) | `""`, rc=0 | `Err` |
| size line with no terminating CRLF (`5hello`) | `""`, rc=0 | `Err` |
| body ends with no last-chunk (`5\r\nhello\r\n`) | `"hello"`, rc=0 | `Err` |
| chunk-data not followed by CRLF | partial, rc=0 | `Err` |
| well-formed body | payload | payload (unchanged) |
| `chunk-ext` on the size line (`5;a=b`) | truncated | payload (now correct) |

The `chunk-ext` row is a fix in the other direction: RFC 7230 §4.1 permits
`chunk = chunk-size [ chunk-ext ] CRLF`, and `headers.spl` had no `;` strip
(only `http1.spl` did), so a legal request was being truncated. Without the
strip, tightening the size check would have turned that silent truncation into a
spurious 400 on a legal request.

### Files changed (full caller family)

- `src/lib/nogc_sync_mut/http/headers.spl`
- `src/lib/gc_async_mut/http/headers.spl`
- `src/lib/nogc_async_mut/http/headers.spl`
- `src/lib/nogc_sync_mut/http/http1.spl` (`decode_chunked` + `decode_chunked_with_trailers`, both exported)
- `src/lib/nogc_async_mut/http_server/parser.spl` (maps `Err` to `ParseError`)
- `src/lib/nogc_sync_mut/http/http_common_hex_spec.spl` (regression cases)

### Verification (seed interpreter — `bin/simple` prints the Rust-seed banner, stage 3 blocked)

Spec: `SPEC FILE VERDICT: ... declared>=15 executed=15 passed=15 failed=0 dropped=0`.

Parser tier (the security-relevant one), `POST` + `Transfer-Encoding: chunked`:

```
before: P2_nonhex  => Ok body=[]      # accepted as an empty body
after:  P2_nonhex  => Err msg=[chunked framing error: invalid chunk size ...]
```

Sabotage, both directions:
- Revert the fix → `A_nonhex=[]`, `B_overlen=[]`, `C_valid=[hello]` — the exact
  original symptom returns.
- Break the good path (drop lowercase from the HEXDIG set) → the valid
  `a\r\n0123456789` example goes red (`expected ERR to equal 0123456789`).
- Break the reject path (`is_hex_digits` always true) → the non-hex example goes
  red (`expected  to equal ERR`), i.e. the negative assertions are not vacuous.

### Not affected

`src/runtime/runtime_native.c:7681 rt_http_decode_chunked` is **correct
already** and was left alone: it uses `strtoull` with a `parse_end == size_text`
check (so a non-HEXDIG size is rejected, not read as the terminator), strips
`;`, bounds-checks the chunk against the buffer, and verifies the CRLF after
chunk-data — returning `0` through its existing bool error channel, which the
caller at :7875 already tests with `if (!...)`.

### Spun out, not fixed here

- `doc/08_tracking/bug/http_parser_chunk_terminator_scan_ignores_chunk_boundaries_2026-08-07.md`
- `doc/08_tracking/bug/try_operator_early_return_matches_neither_ok_nor_err_2026-08-07.md`
