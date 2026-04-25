# Real-demo framebuffer hash pin (replace synthetic 4×4)

**Priority:** low (spec passes; truthfulness gap)
**Filed:** 2026-04-25
**Component:** `test/fixtures/game2d_golden_hello_720p.hash` + `test/util/game2d_pin_golden_hash.spl`
**Discovered by:** game2d-framework SStack Phase 5 / Phase 7

## Description

`AC-5` golden-frame test currently passes against a synthetic 4×4 framebuffer
hash, not the actual `examples/game2d/hello/main.spl` framebuffer. The
`game2d_golden_spec.spl` (11/11) verifies FNV-1a stability and the
hash invariant, so the spec contract holds — but the fixture name implies a
720p real-demo capture, which is the user's likely interpretation.

State file marks AC-5 as **PARTIAL** for this reason.

## Evidence

- `test/fixtures/game2d_golden_hello_720p.hash` = `0x253edd45a462bc15` (synthetic 4×4).
- `test/util/game2d_pin_golden_hash.spl` — documents synthetic 4×4 scope:
  "Phase 3 §G shared fixture is 4×4", "Hash is byte-stable across runs for
  identical inputs (AC-5 contract)".
- `.sstack/game2d-framework/state.md` `### 5c-fix G3`, `### 7-verify-rerun-2 W3`.

## Blockers (must clear before pinning)

1. **`impl X: Trait` engine-block parse error** — `engine/render/headless.spl:212`
   and `backend/sdl_backend.spl` engine-blocks fail to parse, preventing
   programmatic `HeadlessBackend` boot. See ticket
   `game2d_impl_block_parse_repair.md`.
2. **Interpreter bulk-buffer limit** — building a 480k-pixel `[u32]`
   framebuffer (`1280 × 720 × 4`) in `bin/simple run` is infeasible per memory
   `feedback_interpreter_bulk_buffer.md`. Native compile or `rt_*` extern is
   required.

## Suggested fix direction

Once both blockers above are repaired:
1. Run `bin/simple run test/util/game2d_pin_golden_hash.spl --real-demo` (the
   pin script is parameterized).
2. Replace the fixture content with the captured hash.
3. Update `test/util/game2d_pin_golden_hash.spl` documentation to drop the
   "synthetic 4×4" disclaimer.
4. Re-run `test/system/game2d_golden_spec.spl` to confirm 11/11 against the
   real fixture.

## Related

- `doc/08_tracking/bug/game2d_impl_block_parse_repair.md`
- Memory: `feedback_interpreter_bulk_buffer.md`
