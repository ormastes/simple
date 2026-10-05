# Real-site PNGs never decoded: palette PNGs rejected, multi-block DEFLATE refused (2026-10-05)

Status: FIXED (branch `work/png-palette-gray`)

Found while tracing why google.com's logo and the wikipedia.org globe never
paint (gap 2 of the 2026-10-05 five-site re-test). The transport half is
`tls_binary_body_utf8_lossy_2026-10-05.md`; once the bytes arrived intact,
two decoder defects remained.

## 1. Only 8-bit RGB/RGBA PNGs were accepted

`src/lib/common/image/png_decode.spl` rejected every other IHDR with
"PNG bit depth or color type is unsupported". The google logo is an 8-bit
palette PNG (272x92, color type 3); the wikipedia globe also fails the same
check. Palette and grayscale PNGs are extremely common on the web.

Fix: color types 0 (gray, 1/2/4/8-bit), 3 (palette, 1/2/4/8-bit) and 4
(gray+alpha, 8-bit) are decoded, with `tRNS` (per-palette-entry alpha, or
the single transparent gray/RGB value). Packed sub-byte samples are read MSB
first; the filter step uses a byte stride rounded up and a filter unit of at
least one byte (`_png_unfilter`). The 8-bit RGB/RGBA path is unchanged
(plus the optional RGB `tRNS` key). Still rejected, explicitly: 16-bit
samples and Adam7 interlacing. `reconstruct_scanlines` keeps its signature
and checks; it now delegates to `_png_unfilter`.

Spec: `test/01_unit/lib/common/image/png_decode_palette_gray_spec.spl`
(9/9; 2/9 on main -- only the two "still rejected / unchanged" cases).

## 2. DEFLATE back-references into an earlier block were refused

`src/lib/nogc_sync_mut/compression/gzip/inflate.spl` decoded every block
into a fresh buffer, so a length/distance pair reaching into a previous
block failed `distance > out.len()` and the whole stream returned nil.
RFC 1951 §3.2 allows it explicitly ("the distance can refer to a string in
a previous block"), and zlib emits it routinely: the google logo's IDAT is
two dynamic blocks and the second starts with distance 273 into the first.
Any multi-block zlib/gzip payload was affected (PNG, gzip HTTP bodies).

Fix: fixed and dynamic blocks decode after the stream's earlier output
(`history`) and return the whole output; the bound is now applied to the
total stream length rather than recomputed per block (same limit). The
legacy single-block helpers pass an empty history (unchanged).

Spec: `test/01_unit/lib/nogc_sync_mut/compression/gzip_inflate_cross_block_spec.spl`
(3/3; 1/3 on main). The hand-built stream matches Python's
`zlib.decompress(..., -15)`.

## Evidence

Probe pages with only the `<img>` (rendered through the session lane with the
TLS byte fix): the google logo and the wikipedia globe both paint; before,
each failed at the decoder.

## Open, recorded here

- Under JIT (`simple run` without the interpreter fallback) `inflate` on the
  google logo stream still returns nil while the interpreter returns the
  correct 25,116 bytes -- a seed JIT miscompile, not an inflater bug.
  Unblock: reduce `inflate_bounded` to a minimal JIT repro.
- github.com images from `images.ctfassets.net` fail at fetch time with
  "network: Network request failed" (webp/svg; not a decoder issue).
