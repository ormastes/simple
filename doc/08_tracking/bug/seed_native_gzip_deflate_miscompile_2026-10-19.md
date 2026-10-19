# Seed native codegen gives wrong gzip/deflate results

**Date:** 2026-10-19
**Status:** open
**Area:** Rust seed native backend (Cranelift); `src/lib/nogc_sync_mut/compression/gzip/`

## Symptom

The same source gives different output under the interpreter (`run`) and as a
seed-built native binary (`compile --native`):

| Probe | Interpreter | Native (seed bcde7eef and e357ff7f) |
|---|---|---|
| `deflate_block_fixed_sync_flush(lz77_compress(data, 1))`, 300-byte input | 273 bytes | 271 bytes, different content |
| `compression.gzip.compress.gzip_decompress(valid gzip)` | 300 bytes | `nil` |

`lz77_compress` agrees (252 tokens in both), so the encoder fault is in the
fixed-Huffman block writer (`deflate.spl:92 _deflate_block_fixed_ex` and its
helpers). Many of those parameters are untyped (`tokens`, `length`,
`distance`). The decoder fault is somewhere in the member path
(`gzip_header_parse_at` / `inflate_member` / footer validation).
`inflate` by itself decodes a valid stream correctly when compiled natively.

## Not caused by the AotNative gate change

None of these functions were flagged by the standalone-SMF gate before
`efab9d641eb`, and the seed built before that change (bcde7eef) gives the
same wrong output. That change does make these functions reachable from the
compress dynSMF bundle. So a seed-built `compress.smf` compiles, and has all
its exports, but its gzip/deflate results are wrong. The crypto primitives
checked so far (aes256-gcm, chacha20-poly1305, x25519, hmac-sha256) match
the interpreter when compiled natively.

## Repro

```
use std.nogc_sync_mut.compression.gzip.lz77.{lz77_compress}
use std.nogc_sync_mut.compression.gzip.deflate.{deflate_block_fixed_sync_flush}

fn main():
    var data: [u8] = []
    var i = 0
    while i < 300:
        data.push(((i * 7) % 251) as u8)
        i = i + 1
    val out = deflate_block_fixed_sync_flush(lz77_compress(data, 1))
    var s = 0
    for b in out:
        s = (s * 31 + (b as i64)) % 1000000007
    print "out={out.len()} sum={s}"
```

The interpreter prints `out=273 sum=476866860`. The native binary prints
`out=271 sum=137043012`. Run it from inside the repo: compiling from outside
the repo fails stdlib root resolution on the older seed.
