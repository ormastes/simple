# Bug: simple_runner native-build perf/hash gap on macOS

## Status

Open

## Context

While checking pure Simple 2D performance for
`test/perf/graphics_2d/simple_runner.spl`, the hash-correct `bin/simple run`
path remained faster than the current native-build artifacts on macOS.

## Evidence

- `bin/simple run test/perf/graphics_2d/simple_runner.spl --full`
  - Hashes match the C reference:
    - fill `3453644792`
    - blit `1245774277`
    - scroll `35205929`
- `bin/simple native-build --backend cranelift ... && simple_runner_native --full`
  - Hashes match the C reference.
  - Runtime is slower than `bin/simple run` for the same workload on this host.
- `src/compiler_rust/target/debug/simple native-build --backend llvm ... && simple_runner_native_llvm --full`
  - Workload dimensions are now nonzero after avoiding module-global dimensions.
  - Hashes do not match the C reference:
    - fill `2575739855`
    - blit `1763922181`
    - scroll `2026620841`
- `test/perf/graphics_2d/fnv1a_native_repro.spl`
  - Interpreter and LLVM native-build both report `2729900182` for the same
    four packed pixels, so the FNV arithmetic itself is not the isolated bug.
- `simple_runner.spl --full --debug-pixels`
  - Interpreter and LLVM native-build report matching representative pixels for
    p0/pmid/plast in all three scenes, but the full-frame hashes still differ.
  - Region hashes localize divergence:
    - fill row0 matches, but rowmid/rowlast and mid/last windows differ.
    - blit row/window hashes differ even though p0/pmid/plast match.
    - scroll sampled row/window hashes match, but full-frame hash still differs.
  - A 9x9 deterministic sample grid confirms native-render mismatches:
    - fill: 28 sampled mismatches, first at index `259440`
    - blit: 52 sampled mismatches, first at index `240`
    - scroll: 6 sampled mismatches, first at index `259440`
- Conservative experiments that did not fix LLVM native hashes:
  - Returning `Framebuffer` from `do_clear`/`do_rect`/`do_blit` and assigning it
    at call sites.
  - Replacing the 4-pixel rect write unroll with a single-pixel loop.
- `test/perf/graphics_2d/blit_tile_native_repro.spl`
  - Interpreter writes a 256x64 row as four 64-pixel color tiles and reports:
    `p0=4278190335`, `p64=4278255360`, `p128=4294901760`,
    `p192=4278255615`, `p240=4278255615`.
  - LLVM native-build at `--opt-level none` and `--opt-level aggressive`
    receives the correct tile IDs, offsets, and colors, but reports every
    sampled tile as the first blue color:
    `p0=4278190335`, `p64=4278190335`, `p128=4278190335`,
    `p192=4278190335`, `p240=4278190335`.
  - The current repro uses a direct inline write loop in `render_row`, so the
    failure does not require a helper call or return-by-value framebuffer.
- `test/perf/graphics_2d/blit_tile_u64_native_repro.spl`
  - The same row test using `[u64]` packed pixels is interpreter-correct.
  - LLVM native-build at `--opt-level none` still corrupts later samples:
    `p0=4278190335`, `p64=4278190335`, `p128=4278190335`,
    `p192=4278190335`, `p240=536862720`.
  - This rules out `[i64]` alone as the cause and keeps the suspicion on native
    array mutation/lowering/runtime ABI behavior in loop-heavy writes.

## Expected

Optimized native-build output should render the same pixels as the hash-correct
runner path and should not be slower than `bin/simple run` for the same pure
Simple scalar loops.

## Notes

This is not accepted as performance evidence for the GUI/Engine2D NFR until the
native artifact reports matching hashes for all canonical scenes.
