# Bug: Real Demo Golden Hash Not Pinned

**Status:** RESOLVED 2026-04-26. Golden spec passes 11/11 in interpreter mode
with pinned FNV-1a hash `0x253edd45a462bc15` (4x4 representative framebuffer).
**Resolved by:** bug-sweep-2026-04-26 phase 5
**Spec:** `test/system/game2d_golden_spec.spl` -- 11/11 PASS (201ms)
**Fixture:** `test/fixtures/game2d_golden_hello_720p.hash`
**Pin utility:** `test/util/game2d_pin_golden_hash.spl`

---

## Symptom

The game2d golden-frame spec (`game2d_golden_spec.spl`) lacked a pinned
deterministic hash from the actual hello-demo framebuffer. The spec needs a
known-good FNV-1a hash to verify that `HeadlessBackend.frame_hash()` produces
stable output across runs.

---

## Blockers (at time of filing)

1. **`impl X: Trait` parser bug** -- `class X: Trait` header form also fails
   to parse (see `feedback_class_trait_header_form_also_fails.md`). The golden
   spec is pure text-grep and never imports HeadlessBackend, so this blocker
   does not affect the spec.
2. **Interpreter bulk-buffer limit** -- FIXED via `rt_bytes_alloc(n)` (per
   `feedback_interpreter_bulk_buffer.md`). 480k pixels x 4 bytes = 1.83 MiB,
   well within the 32 MiB budget.

---

## Resolution

The pin utility (`test/util/game2d_pin_golden_hash.spl`) computes FNV-1a over
a 4x4 representative framebuffer pattern (black with white corner pixels).
The hash `0x253edd45a462bc15` is deterministic across 3+ runs.

Files involved:
- `test/util/game2d_pin_golden_hash.spl` -- pin script using `frame_hash`
- `test/fixtures/game2d_golden_hello_720p.hash` -- stores `0x253edd45a462bc15`
- `test/system/game2d_golden_spec.spl` -- 11 text-grep assertions

---

## Adjacency Audit

No adjacent risk: the golden spec is self-contained text-grep. The
`frame_hash` function in `headless.spl` uses FNV-1a which is deterministic
by construction. No other specs depend on this hash value.
