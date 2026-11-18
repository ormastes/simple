# Quadratic fragment-accumulator neighbors in networking code
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** OPEN (Site 2 closed 2026-11-18; Site 1 `ssh_session.spl` remains open in SSH lane)
**Found:** 2026-08-21
**Owner:** networking / SSH / HTTP service lanes

## Defect class

Same class as the two closed records
`simpleos_tls_fragment_accumulator_quadratic_2026-08-20.md` and
`simpleos_sftp_fragment_accumulator_quadratic_2026-08-20.md`: a receive
buffer that rebuilds its entire retained prefix on every ingress fragment
(`buf = buf + chunk`, or a full-copy `slice` compaction after each consumed
frame) instead of appending into a bounded ring and advancing a head offset.
Under adversarial one-byte fragmentation this costs O(n^2) byte copies before
a frame is framed.

The fixed reference shape is `SftpSessionV3._append` /
`TlsApplicationRecordStreamV1.ingest`: write each admitted byte once into a
fixed-capacity ring, consume by advancing `head`, never copy the remainder.

## Sites found (2026-08-21 scan of `src/lib/**` networking + `src/os/apps/**`)

1. `src/os/apps/sshd/ssh_session.spl:683,707,718` — encrypted-packet receive
   loop. `self.recv_buf = rt_bytes_concat(self.recv_buf, more)` per fragment,
   plus `_slice_range` full-copy compaction after each packet. Strongest
   match; this is the transport underneath the SFTP owner that was just fixed,
   so SFTP's linear accumulator is still fed by a quadratic stage.
2. `src/lib/nogc_async_mut/http_server/parser.spl:110` — `self.buffer =
   self.buffer + data` in `feed()`, the per-socket-read entry point;
   consumption is also full-copy `slice` (122, 185, 201). Bounded by
   `max_header_line`/`max_body`, so worst case is `(max_body/read_size)^2`
   byte copies. *(CLOSED 2026-11-18 — see follow-up below.)*
3. `src/lib/nogc_async_mut/http_server/parser.spl:200,205` — `self.body =
   self.body + self.buffer` rebuilds the whole accumulated body per feed.
4. `src/lib/nogc_sync_mut/io/tcp.spl:214,251,306` — `buf = buf + chunk` in
   `read_exact` / `read_all` / `read_bytes_or_empty`. `read_all` is worst: no
   size bound at all.
5. `src/lib/nogc_sync_mut/io/pipe.spl:80` — same pattern for stdin
   `read_exact`.
6. `src/os/apps/dbd/dbd.spl:324` — `val updated = self.log_text + line + "\n"`
   then re-encodes and rewrites the whole file per appended journal line. Not
   fragment reassembly, but the same accumulation class; the docstring above
   it already admits the blocker.

## Checked and excluded as benign

- `src/os/apps/dbd/dbd_command_ingress.spl:383` — already a bounded ring with
  in-place byte writes.
- `src/lib/nogc_{async,sync}_mut/io/buffer.spl:295,332` — bounded by
  `buf_size` with a flush before overflow, so copies are O(buf_size).
- `ssh_cipher.spl:228`, `ssh_kex_primitives.spl:147`,
  `ssh_session_helpers.spl:591` — hex-dump builders over fixed-size keys.
- `http/headers.spl:145`, `http/http1.spl:201-211`,
  `http_server/range.spl:136-142` — one-shot response encoders, not
  per-fragment receive paths.
- `websocket/**` — no accumulate-by-concat reassembly buffer present.

## Why recorded rather than fixed here

The two assigned records were closed with evidence in this session. Converting
six further owners to ring accumulators is a large, protocol-behavior-bearing
diff across three service lanes and is out of scope for that change. Site 1 is
the highest priority: it sits directly beneath the accumulator just fixed.

## Disposition 2026-08-21

Binary: `bin/release/x86_64-unknown-linux-gnu/simple` (Rust bootstrap seed).

**FIXED — sites 2,3,4,5.** Concat-per-fragment replaced with amortized append,
matching the `ssh_sftp_v3._append` reference shape:

- `src/lib/nogc_sync_mut/io/tcp.spl:214,252,308` and
  `src/lib/nogc_sync_mut/io/pipe.spl:80` — `buf = buf + chunk` (allocates a new
  array of the full retained length per chunk) became a `for b in chunk:
  buf.push(b)` loop. `[u8].push` is amortized O(1), so `read_exact` / `read_all`
  / `read_bytes_or_empty` go from O(n^2) to O(n) in bytes read. No `extend`
  primitive exists in this tree; the push loop is the established pattern.
- `src/lib/nogc_async_mut/http_server/parser.spl` — the Content-Length body is
  now accumulated into `body_chunks: [text]` with a running `body_len`, joined
  once via `.join("")` on the transition to `ParseState.Complete`. Previously
  `self.body = self.body + self.buffer` rebuilt the entire retained body on
  every feed. `consumed` accounting and the `body` field's observable value are
  unchanged by construction.

**NOT fixed — buffer re-slicing in the same parser *(superseded 2026-11-18; fixed below)*.** `self.buffer =
self.buffer.slice(k, len)` after each consumed line/frame still copies the
remainder, and `self.buffer = self.buffer + data` still concatenates per feed.
Removing those needs a read-offset cursor rather than a re-sliced string, which
changes `feed`'s `consumed` contract; deferred rather than risked here.

**NOT fixed — site 6 (`dbd.spl:324`), reclassified.** This is not a fragment
accumulator and the concat is not the dominant cost. Every mutation rewrites
AND re-reads the whole journal through `g_vfs_write_file_bytes` /
`g_vfs_read_file_bytes`; the `log_text + line` concat is negligible beside that.
The function's own docstring already names the real blocker — the absence of a
crash-atomic append+sync VFS primitive. Fixing the concat alone would be
cosmetic and would falsely suggest the O(total journal bytes) per-operation
blocker had been addressed. Leave for the DBFS/VFS lane.

**NOT fixed — site 1 (`ssh_session.spl:683,707,718`), excluded by coordinator.**
Owned by the SSH transport lane and dispatched separately. Still the highest
priority: it is the quadratic stage feeding the now-linear SFTP accumulator.

## Test evidence

- New: `test/01_unit/lib/nogc_async_mut/http_server/body_fragment_accumulation_spec.spl`
  -> `Results: 4 total, 4 passed, 0 failed` / `PASS`.
- Regression: `test/01_unit/lib/nogc_sync_mut/io/buffer_spec.spl`
  -> `Results: 2 total, 2 passed, 0 failed` / `PASS`.

**Honest limitation on the "failing-before" bar.** These refactors are
behavior-preserving, so the new spec passes both before and after — it is a
regression guard on the observable contract, not a fail-before-fix reproduce.
A genuine failing-before test needs work counters on the accumulator (the
`SftpAccumulatorWorkV3` pattern); that public surface was judged out of scope
for a "smallest correct diff" change and is NOT claimed as delivered here.

## Work counters + fail-before evidence 2026-08-21

The earlier "regression guard only" caveat is now closed. Minimal internal
counters were added and the specs were executed against BOTH shapes.

- `src/lib/nogc_sync_mut/io/byte_append.spl` (new) — `io_append_chunk(buf,
  chunk)` appends in place and returns bytes copied by that call. `tcp.spl`
  (:214,:251,:306) and `pipe.spl:80` now call it; they ignore the return, so
  the counter is a test hook, not public API.
- `parser.spl` — internal `body_copy_bytes` plus `body_copy_work()`.

**Fail-before (pre-fix concat cost restored, then reverted):**
`Results: 7 total, 4 passed, 3 failed` / `FAIL`, exit 1.
- `copies O(n) bytes appending n one-byte chunks` -> `expected false to equal true`
- `keeps append work linear as fragment count doubles` -> **`expected 2080 to
  equal 1056`** (2080 = 64*65/2, the quadratic sum; linear is 2*528)
- `copies O(n) body bytes when the body is fed one byte at a time` ->
  `expected false to equal true`

**Pass-after (shipped code):** `Results: 7 total, 7 passed, 0 failed` / `PASS`.

The 4 correctness scenarios pass in BOTH shapes, confirming the refactor is
behavior-preserving and that only the 3 work-counter scenarios discriminate.
Regression: `io/buffer_spec.spl` PASS.


## Follow-up 2026-10-30: `io_append_chunk` never appended (removed)

`io_append_chunk(buf, chunk)` pushed into its `buf` PARAMETER. In the interpreter lane arrays are
values (doc/07_guide/language/value_semantics_by_engine.md), so on the
interpreter the push never reached the caller: measured `copied=1 len=0`.
Every converted reader (`TcpStream.read_exact` / `read_all` /
`read_line_bounded`, `tcp_fd_read_line_or_empty`,
`tcp_fd_read_bytes_or_empty`, `Stdin.read_exact` (pipe.spl)) therefore returned an EMPTY
buffer. Fix: each reader now appends through its own binding
(`for b in chunk: buf.push(b)`), still linear, and `byte_append.spl` is
deleted. Specs: `test/01_unit/lib/nogc_sync_mut/io/stream_reader_append_shape_spec.spl`
(in-place shape + no array-parameter helper) and
`test/01_unit/lib/nogc_async_mut/http_server/body_fragment_accumulation_spec.spl`
(linear copy work as fragment count doubles).


## Follow-up 2026-11-18: Site 2 closed — `HttpRequestParser` O(N) chunked ingress & `buf_pos` cursor (Wave C7)

Closed the deferred `self.buffer = self.buffer + data` per-feed concatenation
and per-line `self.buffer = self.buffer.slice(...)` rewrites in
`src/lib/nogc_async_mut/http_server/parser.spl` while preserving constructor
and `consumed`-byte contracts:

- **O(1) fragment ingress (`rx_chunks: [text]`, `rx_pending_bytes: i64`):**
  non-empty `feed(data)` chunks append to `rx_chunks` in O(1). Partial lines
  without `"\n"` stay queued without copying while streaming line-length bounds
  (`431` / `413`) are enforced from `(buffer.byte_len() - buf_pos) + rx_pending_bytes`.
- **Direct body drain:** when in `ParseState.Body` (`Content-Length`), queued
  `rx_chunks` drain straight into `body_chunks` without touching `self.buffer`,
  splitting only a boundary chunk that carries pipelined bytes of the next
  request.
- **`buf_pos: i64` cursor + lazy compaction:** `RequestLine` and `Headers` scan
  from `buf_pos` (`buffer.index_of("\r\n", buf_pos)`) and advance
  `buf_pos = line_end + 2` without rewriting `self.buffer` per header,
  compacting only when `buf_pos >= 4096 and buf_pos * 2 >= buffer.byte_len()`
  (or dropping `buffer = ""` at zero unread bytes) and on `reset()`.
- **Work counter (`pub header_copy_bytes: i64`):** tracks cumulative bytes
  materialized/compacted in `self.buffer` during request-line and header
  framing, proving linear O(N) scaling across 8 KiB and 16 KiB 64-byte
  fragmented multi-header and single-header streams plus pipelined bodies.
- **Consistent byte units & nil-free surface:** all text lengths/cuts in
  `parser.spl` use `byte_len()` (`check-text-len-unit-mix.shs` 0 unit-mix,
  0 `len()`-bounded rows) and zero `nil` outside `unsafe:`.

### Verification (2026-11-18)

- `TEXT_LEN_BASELINE=/dev/null TEXT_LEN_MIX_BASELINE=/dev/null sh scripts/check/check-text-len-unit-mix.shs src/lib/nogc_async_mut/http_server/parser.spl`
  -> `PASS — 27 function(s) checked, 0 unit-mix + 0 len()-bounded row(s) all baselined, 0 new, 0 stale`.
- `SIMPLE_LIB=src phase1_artifacts\simple.exe test test/01_unit/lib/nogc_async_mut/http_server/async_parser_limits_spec.spl --mode=interpreter`
  -> `32 total, 32 passed, 0 failed` (`outcome=OK`).
- Regressions (`--mode=interpreter`): `body_fragment_accumulation_spec.spl`,
  `header_block_reassembly_spec.spl`, `async_header_lexical_contract_spec.spl`,
  `chunked_body_boundary_spec.spl`, `chunked_size_overflow_spec.spl` -> all `PASS`.
