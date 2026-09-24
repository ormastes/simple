# AVX-512 native remaining limits (2026-09-10)

Status: known issues on `review/avx512-simd-wip-20260909`.

## Non-AVX-512 routing safety

`x86_avx512_handles` currently claims every SIMD MIR operation, including
operations whose locals have no 512-bit shape. `isel_block_with_x86_simd` can
therefore route ordinary AVX2/SSE operations through the AVX-512 frame owner
when `avx512_shapes` is empty. A non-AVX-512 host may then panic on a missing
frame shape or emit a 64-byte operation. The owner must reject empty shape sets
and only claim operations whose participating locals belong to the AVX-512
frame. Add forced-disabled and mixed-width regressions.

## Native ABI and allocation limits

- AVX-512 vector arguments and return values are rejected by
  `x86_64_avx512_isel.spl`; the native vector ABI is not implemented.
- General-purpose-register spills in the AVX-512 allocator still panic.
- Explicit 512-bit MIR rejects compilation when AVX-512 is unavailable. The
  native path does not automatically scalarize or select the portable
  interpreter fallback.

## Verification limits

- The existing owner-routing test covers scalar constants and `Vec16i`, but
  does not cover `Vec8f`, `Vec8i`, an empty shape map, or mixed AVX2/AVX-512
  functions.
- The draft branch contains the pure-Simple selector, lowerer, encoder, and
  interpreter, but also includes runtime C capability probes and Rust bootstrap
  glue. It is therefore not yet a wholly pure-Simple implementation boundary.
- The branch must be rechecked against current `main`; its open PR was based on
  an older commit and reported conflicts and a failing publish check.

