# LZMA2 — Full LC/LP/PB Property Support

- **Filed:** 2026-05-01
- **Owner:** common compression framework
- **Status:** IMPLEMENTED 2026-05-29
- **Companion landing:** Range-coded LZMA2 decode landed 2026-05-01, restricted to
  `LC=3, LP=0, PB=2` (props byte `0x5D`). Full lc/lp/pb support landed 2026-05-10
  via the restored `std.common.compress.lzma2` hosted XZ bridge. See
  `src/lib/common/compress/lzma2.spl`.

## Context

The pure-Simple LZMA2 decoder previously rejected every range-coded chunk with
`UnsupportedFeature("lzma2 range-coded compressed chunks are not supported")`,
which prevented decoding any stream produced by the host `xz` tool.

To clear the verify-report `[FAIL] src/lib/common/compress/lzma2.spl:330` line in
`doc/09_report/verify_common_compression_framework.md` we landed a pure-Simple
range decoder + LZMA decoder restricted to the `xz` default of
`LC=3, LP=0, PB=2`. This is the only configuration emitted by `xz -z` at the
default preset, so it covers the practical interop surface.

The decoder now delegates hosted XZ/LZMA2 decode to the system `xz` command,
so valid LC/LP/PB combinations accepted by liblzma are accepted by this module
instead of being rejected by the former 3/0/2-only guard.

## Implementation Note

The current implementation is a hosted bridge, not a freestanding pure-Simple
range decoder. It restores the public module, facade routing, XZ magic
detection, compression/decompression entrypoints, and full LC/LP/PB behavior
for hosted tests and tools. A future freestanding decoder can replace the
bridge behind the same API.

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

- [x] Decoder accepts every `props_byte < 9*5*5` value with `lc + lp <= 4`.
- [x] Round-trip parity verified against host `xz` for at least three
      non-default presets that exercise distinct LCLPPB tuples (e.g.
      `lc=4 lp=0 pb=2`, `lc=2 lp=2 pb=2`, `lc=3 lp=0 pb=4`).
- [x] Spec coverage extended in `test/unit/lib/common/lzma2_range_coded_spec.spl`.
- [x] The `UnsupportedFeature("LZMA2 LCLPPB other than 3/0/2")` site in
      `src/lib/common/compress/lzma2.spl` is removed.

## Related

- Verify report — `doc/09_report/verify_common_compression_framework.md`
- Feedback note — `feedback_compile_mode_false_greens.md` (interpreter must be
  source of truth for compression specs)
- Feedback note — `feedback_interpreter_bulk_buffer.md` (if perf becomes the
  blocker, route through `rt_bytes_alloc`)
