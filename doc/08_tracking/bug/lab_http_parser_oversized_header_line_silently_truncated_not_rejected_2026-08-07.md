# HTTP parser's "431 Header line too long" guard never fires — the runtime line reader silently truncates first

**Found:** 2026-08-07, during notebook-lanes H3 verification
(`test/03_system/tools/simple_lab/lab_robustness_spec.spl`, fuzz-lite corpus).

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 02).
runtime change needed. The truncation IS detectable from the caller side:
`TcpStream.read_line()` returns the line *including* its terminating newline,
so a runtime-truncated line has a unique signature — raw length >= the
runtime's 8192-byte cap AND no trailing `\n` (a legitimate at-cap line ends in
`\n`; a short EOF-cut line is under the cap). `parser.spl` now checks
`line_truncated_by_runtime(raw)` on both the request line and every header
line before trimming, and rejects with `431 ... truncated at 8192 bytes
without a newline`. Supporting changes: `HttpStatus.RequestHeaderFieldsTooLarge`
(431) added to `src/lib/nogc_sync_mut/http_server/types.spl`, and
`lab_server.spl`'s `_lab_status_from_parser_error` maps the `431` prefix to it
(previously fell through to 400). Verified over real loopback:
`test/03_system/tools/simple_lab/lab_hardening_spec.spl` ("rejects an
oversized header line with 431 instead of silently truncating it") — 8/8
green; the `lab_robustness_spec.spl` fuzz-lite example's formerly-RED 4xx
assertion now expects 431. `TcpStream`/`read_line` semantics unchanged for all
other callers.

## Symptom

`GET /api/lab/status` with one header line ~20000 bytes long (well over the
8192-byte `MAX_HEADER_LINE` cap) gets a normal `200 OK`, not the `431`/4xx the
parser's own bound is supposed to produce. Reproduced directly against
`lab_server.spl` (bypassing the test harness) with a raw socket: same result,
`200`.

## Root cause

`src/lib/nogc_sync_mut/http_server/parser.spl:79` checks
`if hl.len() > max_header_line: return Err("431 Header line too long: ...")`
against the string `read_line()` returns. But the runtime primitive backing
`TcpStream.read_line()` —
`read_line_chunked` in `src/compiler_rust/runtime/src/value/net_tcp.rs:544` —
has its own hidden cap:

```rust
if newline_at.is_some() || total >= 8192 {
    break;
}
```

It stops reading (and returns whatever it has, no error) once it has read
8192 bytes **even if no `\n` was found yet** — i.e. it silently truncates an
over-length line at exactly the same 8192-byte boundary the caller's length
check is trying to catch. `read_line()` then hands back a line of **exactly**
`max_header_line` bytes (never `> max_header_line`), so
`parser.spl`'s `hl.len() > max_header_line` check can never be `true` for a
line the runtime already truncated at that boundary — the check is
structurally unreachable for this failure mode.

The remaining tail of the original oversized line (the rest of the 20000
`x` characters plus the real header's trailing `\r\n`) then gets read on the
*next* `read_line()` call and is treated as a **separate** header line. It has
no `:` in it, so `parser.spl`'s `if colon > 0:` guard silently drops it (not
an error, just not added to `headers`) — the connection proceeds as if the
oversized header never happened, hence the `200`.

## Impact

Not a crash/hang — `lab_server.spl` stays up and answers subsequent requests
correctly (confirmed in the same fuzz-lite run: the final
`GET /api/lab/status` after this case still returns `200` with the right
protocol header). So this does **not** violate the H3 "zero panics" bar. But
it does mean the design's oversized-header bound
(`doc/05_design/app/tools/notebook_lanes_architecture.md` §8.1/§8.5,
"oversized headers ... must produce 4xx") is not actually enforced —
`max_header_line`/`MAX_HEADER_LINE` is dead weight against this exact input
shape, and any header whose value happens to be exactly-8192-bytes-or-more
gets silently mangled into a dropped header rather than rejected.

The count-based guard (`> max_header_count`, "431 Too many headers") is
**not** affected — it operates on a running counter across well-formed short
lines and is unaffected by the chunked reader's per-line truncation.

## Suggested fix

`read_line_chunked` (Rust runtime) needs to distinguish "found a newline
within the cap" from "hit the cap without a newline" and surface the latter
as an error (or a truncation flag) instead of silently returning a
partial, non-terminated line indistinguishable from a short line. That is a
native-runtime change (`src/compiler_rust/runtime/src/value/net_tcp.rs`), out
of scope for the pure-Simple `parser.spl`/H3 evidence work that found it.

## Where this was found

`test/03_system/tools/simple_lab/lab_robustness_spec.spl` ("fuzz-lite corpus"
example) exercises this directly; the spec records it as a known gap
(`fuzz_fail oversized_header status=200 ok=true` in the H3 evidence log)
rather than silently treating a `200` as a pass. See
`doc/09_report/notebook_lanes_robustness_evidence_2026-08-07.md`.
