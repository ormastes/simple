# Seed native codegen gives wrong gzip/deflate results

**Date:** 2026-10-19
**Status:** open. `gzip_*`/`deflate_*` are withheld from the compress dynSMF
bundle (`src/lib/common/compress/dynsmf_entry.spl` and the `compress` manifest
row in `src/os/smf/dynsmf_session.spl`) until this is fixed.
**Area:** Rust seed native backend; `src/lib/nogc_sync_mut/compression/gzip/`

## Symptom

On a 300-byte input, `deflate_compress` / `gzip_compress` compiled with
`compile --native` give 271 / 285 bytes. The interpreter gives 273 / 287
bytes, and those are valid: zlib decodes them back to the input. zlib decodes
the native raw-deflate output to the wrong bytes (the first wrong one is at
offset 8: 7 instead of 56), and rejects the native gzip output (`incorrect
data check`). Native zstd, lz4, snappy, brotli and xz round trips are
byte-identical to the interpreter. Fixing `?` (`490df0ed248`) does not change
any of this.

## Root cause

A `u8` read from a `[u8]` through an untyped receiver is stored raw in an
untyped array literal. A later typed read then decodes it as a tagged int.

```
fn mk_untyped(data):
    var tokens = []
    tokens.push([0, data[0], 0])
    tokens

fn main():
    val d: [u8] = [56u8, 57u8]
    val tok = mk_untyped(d)[0]
    val c: i64 = tok[1]
    print "c={c}"
```

The interpreter prints `c=56`. Native prints `c=7`, both before and after
this lane's changes. A raw byte 56 (`0b111000`) has the TAG_INT bit pattern
for 7. With a typed `data: [u8]` parameter the value is correct.
`lz77_compress(data, level)` (untyped) builds literal tokens as
`[0, data[pos], 0]`, so every literal byte that is a multiple of 8 is encoded
wrong. Fixing it means making byte-array elements box consistently on the
untyped `rt_array_get` / array-literal path. That is not a contained change
(MIR/codegen representation of `[u8]`), so the exports are withheld instead.

The native gzip *member decoder* (`compression/gzip/compress.spl:104`) also
returns nil on valid input. It goes through the same untyped `data` helpers
(`gzip_header_parse_at` etc.), so it is most likely the same defect. That
has not been proven separately.

## Related native gaps seen in the same lane (not fixed)

- `if val x = a:` with `a: [u8]?`: `x.len()` prints `0.0` natively (it should
  be the length); element reads are correct. This happens before and after
  this lane's changes.
- `[v; n]`: when `v` has side effects, native evaluates it `n` times (the
  unrolled literal) and the interpreter evaluates it once. `[v; -1]` gives an
  empty array natively and an error in the interpreter.
- `?` on a bare present non-enum value held as `ANY` reads as nil natively.
  The interpreter rejects `?` on such a value, so there is no defined result
  to match.
