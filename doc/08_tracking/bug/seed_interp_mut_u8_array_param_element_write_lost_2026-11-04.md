# Seed interpreter: element writes into a `mut pixels: [u8]` parameter never reach the caller

- **Filed:** 2026-11-04 (vkfont3 lane)
- **Status:** OPEN — seed (Rust) interpreter defect; not fixed here (seed is
  bootstrap-only and owned by the bootstrap lane; no admitted self-hosted macOS
  binary exists to run the same check on).
- **Platform:** aarch64-apple-darwin, seed `release100-7a0e6fe516f-20261031`
- **Blocks:** acceptance item 7 of
  `macos_vulkan_2d_vector_font_empty_batch_native_fault_2026-07-26.md`
  (`simple test` runs specs on the interpreter).

## Repro

```simple
fn fill(mut meta: [i64], mut pixels: [u8]):
    var i: i64 = 0
    while i < pixels.len():
        pixels[i] = 200u8
        i = i + 1
    meta[0] = 7

fn main():
    var m: [i64] = [0; 4]
    var p: [u8] = [0u8; 5]
    fill(m, p)
    print "m0={m[0]} p0={p[0]}"
main()
```

| mode | output |
|---|---|
| `simple run` (JIT, default) | `m0=7 p0=200` |
| `SIMPLE_EXECUTION_MODE=interpreter simple run` | `m0=7 p0=0` |

The `[i64]` out-param writes back; the `[u8]` one does not (same for a
single indexed store, and for a cross-module callee).

## Impact

`sfnt_render_glyph_into(..., mut meta: [i64], mut pixels: [u8])`
(`src/lib/common/encoding/sfnt_glyf.spl:799`) counts its coverage into
`meta[9]` (64 for '2' at 18 px) but the caller in
`FontRenderer` (`font_renderer.spl:1888`) sees an all-zero `direct_pixels`.
Every atlas cell becomes `0x00FFFFFF` (alpha 0), so under `simple test` every
TrueType glyph is fully transparent on every backend; CPU oracle and GPU then
agree on an all-blank frame.

## Fix direction

Interpreter argument passing for `[u8]` arrays (likely the packed byte-array
value representation) must alias the caller's array like `[i64]` does, on the
plain Simple-function call path in `src/compiler_rust/compiler/src/interpreter_call/`.
Do not rewrite `sfnt_render_glyph_into` around it.
