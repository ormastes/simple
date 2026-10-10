# HIR cache envelope reader

Scope: source-only repair of the seed-generated native cache-envelope ABI
blocker recorded in `../08_tracking/bug/bootstrap_hir_cache_warning_cursor_2026-10-11.md`.
This is separate from the completed three-cycle HIR serialization investigation.
No additional construction or native qualification is authorized by this design.

The existing frame is `header LF W LF count LF escaped-warning LF ... HIR-body`.
Header includes codec and producer/source authority; the HIR body must survive
envelope parsing byte for byte. Its final newline and any extra trailing bytes
are significant to strict HIR admission. The writer and format version remain
unchanged.

## Proven blocker and chosen parser

The observed native loader passes a tagged inferred cursor to a raw-offset text
search, then consumes the raw result as a tagged slice bound. An unrelated MIR
repair cannot repair the already seed-generated compiler's machine code. The
cache protocol should use the shared typed line reader already used by HIR,
instead of introducing another raw-offset text cursor.

`FlatPoolReader.new_canonical` supplies a line array, typed position, strict
integer parsing, count bounds and truncation state. A small pure envelope
parser takes the raw entry and expected header, and returns optional body plus
warnings. It performs no file I/O and changes no identity or cache state.

1. Create the canonical reader. Require its initial `ok` state and
   `reader.lines.join("\n") == raw`. The second check is a fail-closed provider
   contract: split must preserve every field, including the final empty field.
2. Read and compare the exact header and exact `W` marker using `next()`.
3. Read `next_len()`. Counts must be canonical, nonnegative, in range and no
   larger than the remaining line count. A truncated or invalid count fails
   before a warning loop. Valid producer counts, including zero and three,
   retain their existing decimal representation.
4. Read exactly that many warning lines and apply the existing
   `flat_pool_unescape`; warning escape semantics do not change.
5. Copy every remaining line without normalization or decoding, including all
   empty fields, and join with LF. Refuse an empty body.
6. The loader passes those exact bytes to `hir_module_decode_stable`. Only its
   success publishes warnings and increments the hit counter.

## Byte-preservation argument

Let `L = split(raw, LF)` and let `p` be the reader position immediately after
the last warning. Admission first establishes `join(L, LF) == raw`. Header,
marker, count and warnings consume complete fields, so the body begins at field
`p`. Joining `L[p..len]` with LF is exactly the suffix following that envelope
delimiter. No field is filtered, unescaped or normalized. Terminal empty fields
are retained; therefore an extra trailing LF remains extra and the HIR decoder
can reject it. Unicode and literal backslashes in the body are unchanged.
If a provider loses a split field, the full-frame identity check rejects it.

## Ownership, cost and validation

The helper executes inside the loader's existing scratch scope. Split storage,
the identity-check join, warning array, body join and codec temporaries remain
owned by that scope. The existing normal-loader promotion and shard-owned-scope
protocol are unchanged. Failed parses publish neither warnings nor modules.
The full join is one additional linear scan/allocation; no performance claim is
made before qualification. Source authority, keys, store order and strict codec
checks are unchanged.

Pure parser regressions cover three escaped warnings, Unicode/backslash body,
zero warnings, exact terminal/extra LF preservation, stale header, wrong marker,
invalid/negative/overflow/oversized counts, missing newline and missing body.
The actual native store/load spec uses three warnings and retains its positive
optional result across missing, stale and unstable entries, verifying warnings
and scratch reuse after each call. These regressions are authored only; execution
remains pending a separately authorized qualified native runner/construction.
