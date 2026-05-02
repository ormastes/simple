# LZMA2 — Full LC/LP/PB Property Support (Deferred)

- **Filed:** 2026-05-01
- **Owner:** common compression framework
- **Status:** OPEN
- **Companion landing:** Range-coded LZMA2 decode landed 2026-05-01, restricted to
  `LC=3, LP=0, PB=2` (props byte `0x5D`). See
  `src/lib/common/compress/lzma2.spl` (`_lzma_decode_chunk_3_0_2`).

## Context

The pure-Simple LZMA2 decoder previously rejected every range-coded chunk with
`UnsupportedFeature("lzma2 range-coded compressed chunks are not supported")`,
which prevented decoding any stream produced by the host `xz` tool.

To clear the verify-report `[FAIL] src/lib/common/compress/lzma2.spl:330` line in
`doc/09_report/verify_common_compression_framework.md` we landed a pure-Simple
range decoder + LZMA decoder restricted to the `xz` default of
`LC=3, LP=0, PB=2`. This is the only configuration emitted by `xz -z` at the
default preset, so it covers the practical interop surface.

Any other LCLPPB combination is rejected with the explicit error string

```
UnsupportedFeature("LZMA2 LCLPPB other than 3/0/2")
```

so callers cannot silently produce wrong output, and the verify report is honest.

## Why Defer the General Case

A full LCLPPB-agnostic decoder requires:

- A `literal_probs` table sized `0x300 << (LC + LP)` (up to `0x300 << 8 = 196608`
  u16 slots when `LC+LP=8`), versus `0x300 << 3 = 6144` slots in the 3/0/2
  build.
- Position-mask shifts (`LP`, `PB`) to be parameterised through the inner hot
  loops rather than constant-folded.
- Wider interpreter-mode performance budgets — even 6144-slot table init through
  push-loops is on the edge of acceptable per `feedback_interpreter_test_limits.md`
  and the larger tables push into "minutes" territory until `rt_bytes_alloc`-style
  bulk u16 allocation lands.

We chose to ship the 3/0/2 path now, document the limitation, and revisit when
either a) interpreter perf for prob-table init improves, or b) a real consumer
needs a non-default LCLPPB stream.

## Known Caveat — Multi-Chunk Dict Reset

The current implementation reuses the block's accumulating output buffer as
the LZMA dictionary. For default `xz -z` output every block has a single
range-coded chunk with `resets_dictionary` set, so a chunk-internal dict
reset never collides with prior bytes. Streams with multiple chunks per block
that issue a mid-block `resets_dictionary` (control byte 0xE0..0xFF after the
first chunk) would incorrectly let later distance references reach back into
the pre-reset bytes. This is out of scope for the partial landing; defer
together with full-LCLPPB support.

## Acceptance Criteria for Closing

- [ ] Decoder accepts every `props_byte < 9*5*5` value with `lc + lp <= 4`.
- [ ] Round-trip parity verified against host `xz` for at least three
      non-default presets that exercise distinct LCLPPB tuples (e.g.
      `lc=4 lp=0 pb=2`, `lc=2 lp=2 pb=2`, `lc=3 lp=0 pb=4`).
- [ ] Spec coverage extended in `test/unit/lib/common/lzma2_range_coded_spec.spl`.
- [ ] The `UnsupportedFeature("LZMA2 LCLPPB other than 3/0/2")` site in
      `src/lib/common/compress/lzma2.spl` is removed.

## Related

- Verify report — `doc/09_report/verify_common_compression_framework.md`
- Feedback note — `feedback_compile_mode_false_greens.md` (interpreter must be
  source of truth for compression specs)
- Feedback note — `feedback_interpreter_bulk_buffer.md` (if perf becomes the
  blocker, route through `rt_bytes_alloc`)
