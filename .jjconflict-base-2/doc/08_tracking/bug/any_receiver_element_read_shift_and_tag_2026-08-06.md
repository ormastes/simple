# Reading an element off an `any` receiver: three forms, three different results

**Filed:** 2026-08-06 · **Severity:** high (silent wrong data, no diagnostic)
**Found by:** WS-D 2D perf work (`src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl`)
**Engine:** JIT (Cranelift) via `bin/release/x86_64-unknown-linux-gnu/simple`
(md5 `ed53cc5f255e269ca27c4cd83b17aef9`) — note this deployed binary is a **Rust
seed build**, it prints `seed_warning.rs`'s banner.

## Reproduction

```simple
fn probe(mut dst: any, idx: i32):
    val a = dst[idx]
    val b: u32 = dst[idx]
    val c: i64 = dst[idx]
    val e = dst[idx] as u32
    var tmp: [u32] = [0; 1]
    tmp[0] = dst[idx]
    println("raw=" + a.to_text() + " u32=" + b.to_text() + " i64=" + c.to_text() + " cast=" + e.to_text() + " via_arr=" + tmp[0].to_text())
    println("shift_raw=" + ((a >> 24) & 0xFF).to_text() + " shift_u32=" + ((b >> 24) & 0xFF).to_text() + " shift_arr=" + ((tmp[0] >> 24) & 0xFF).to_text())

fn main():
    var d: [u32] = [0x11405060 as u32; 1]
    probe(d, 0)
```

Observed (`bin/simple run`):

```
raw=289427552 u32=2315420416 i64=2315420416 cast=289427552 via_arr=289427552
shift_raw=0.000...067  shift_u32=138  shift_arr=17
```

Expected: every form yields `289427552` (`0x11405060`), and every shift yields `17`.

## Three distinct defects in one expression

| form | value | `>> 24 & 0xFF` | verdict |
|------|-------|----------------|---------|
| `val a = dst[idx]` | correct | **a decimal fraction** (`0.0…067`) | integer shift produced a float |
| `val b: u32 = dst[idx]` | **`value << 3`** (tagged word) | 138 | type annotation returns the tag, not the value |
| `val c: i64 = dst[idx]` | **`value << 3`** | — | same |
| `val e = dst[idx] as u32` | correct | — | only correct form |
| `tmp[0] = dst[idx]` (typed array slot) | correct | 17 | correct |

The `val b: u32 = …` case is the most dangerous: an explicit, apparently
tightening annotation is the one that yields the *tagged* representation.

## Impact found in the field

`simd_kernels.spl:_scalar_blend_row` used `val d = dst[idx]` and then
`(d >> 24) & 0xFF` for the destination alpha. Every scalar-fallback alpha blend
in the software rasterizer produced wrong pixels: with `da=17` the code read
`138`, giving `out_a = 145` instead of `32`. **210 of 256 sampled (sa, da) pairs
disagreed with the C kernel.** Fixed there by switching to `as u32`; the generic
defect is unfixed.

Repro probe (parity, dense over `da`, `sa` at 0/1/2/127/128/253/254/255):
`test/perf/graphics_2d/blend_parity_probe.spl` — `PARITY_DIFFS=210` before,
`0` after.

## Ask

1. `(any_value >> n)` must not lower to floating-point.
2. `val x: u32 = any_arr[i]` must untag exactly like `as u32` does.
3. Until fixed, `as u32` (or a typed-array temporary) is the only safe read.
   Audit other `: any` framebuffer/byte-buffer parameters that do bit
   arithmetic on element reads.
