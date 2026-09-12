# Vulkan `_glsl_blit()` carried the pre-unpremultiply src-over formula while the device blob carried the frozen CPU one (2026-09-12)

**Status:** FIXED (GLSL corrected, blob regenerated from it, byte-level pin guard added,
device evidence recorded, stale doc anchors corrected).
**Area:** `src/lib/gc_async_mut/gpu/engine2d/` — Vulkan image src-over kernel.
**Parent:** F27 of `doc/08_tracking/bug/metal_engine2d_readback_device_defects_2026-09-12.md`.

## The frozen oracle

`blend()` in `src/lib/**/engine2d/color.spl` composites in premultiplied space and
unpremultiplies by the *resulting* output alpha:

```
inv        = 255 - sa
dst_weight = (da * inv) / 255          # dst's premultiplied contribution, 0..255 basis
out_a      = sa + dst_weight
out_c      = (sc * sa + dc * dst_weight) / out_a      # per channel
```

with early-outs `sa == 255 -> src` (raw store) and `sa == 0 -> dst`. For
`0x01020304` over `0x10203040`: `inv = 254`, `dst_weight = (16*254)/255 = 15`,
`out_a = 16`, channels `(30, 45, 60)` — i.e. **`0x101E2D3C`**.

The superseded *pre-unpremultiply* formula uses `inv` in the channel numerators and
divides by the constant 255, giving **`0x101F2F3F`**. The two agree exactly when the
destination is opaque (`da == 255`), which is why a stale copy can survive a long time:
most test grounds are opaque.

## What was actually wrong

Three things were claimed to be in agreement. Measured, they were not:

| artifact | formula it carried | value for the anchor |
|---|---|---|
| CPU `color.spl` `blend()` | frozen (premultiplied + unpremultiply) | `0x101E2D3C` |
| Metal kernel | frozen | `0x101E2D3C` |
| `spirv_blit()` blob (the words the Vulkan device runs) | frozen | `0x101E2D3C` |
| `_glsl_blit()` GLSL text (`backend_vulkan_glsl.spl:638-651`) | **pre-unpremultiply** | `0x101F2F3F` |

So the **device was already correct** and F27's note that
`backend_vulkan_spirv_raster_blobs.spl:2145` "claims CPU parity" was accurate — the blob
had carried the frozen formula since 2026-08-08. Verified directly by disassembling the
committed blob with `spirv-dis`: `%162 = UDiv(IMul(dst_a, inv), 255)` is `dst_weight`,
`%163 = IAdd(sa, %162)` is `out_a`, and all three channel numerators multiply the
destination channel by `%162` before dividing by `%163`.

The defect was that the **readable source of truth disagreed with the thing that runs**,
and nothing in the tree could tell. That is worse than a wrong kernel, because the next
person to regenerate the blob from the GLSL — the obvious, documented-looking move —
would have silently *introduced* the regression into the device path.

**Root cause of the drift:** the blob was hand-assembled. Its own docstring said
"Regenerated via spirv-dis/spirv-as", i.e. the 2026-08-08 fix was applied by patching
SPIR-V directly and never flowed back into the GLSL. A derived artifact that is edited
by hand has no derivation left to check.

## Fix

1. **GLSL corrected** (`backend_vulkan_glsl.spl`, `_glsl_blit()`): introduces
   `dst_weight`, uses it in the alpha accumulation *and* all three channel numerators,
   and divides each channel by `out_a`. Integer arithmetic is identical to `color.spl`
   line for line, including truncation order. The `sa == 255` raw-store and `sa == 0`
   early-outs already matched and are unchanged.
2. **Blob re-derived, not hand-patched**: `scripts/tool/gen-blit-spirv.shs` extracts the
   GLSL through `scripts/tool/extract-blit-glsl.shs`, compiles it with
   `glslangValidator -V --target-env vulkan1.1`, runs `spirv-val`, transcribes with the
   existing `scripts/tool/spirv-to-spl-words.shs`, and rewrites the `spirv_blit()` array
   plus a `# sha256:` pin line in place. The committed blob is now
   `db0bbeb4a0dea497645164d50fc5f98ada28b5d3e66a8f9f363e402a99a4a793` (6848 bytes).
   It is larger than the old hand-assembled 4016 bytes (glslang emits debug names and
   unoptimised control flow); it is semantically the same kernel, and device evidence
   below is what settles that, not the byte count.
3. **Pin guard added**: `scripts/check/check-blit-spirv-pinned.shs`, a sibling of
   `check-rect-batch-spirv-pinned.shs`, recompiles the committed GLSL and compares byte
   body and sha against the committed blob. Same verdict convention as the pre-push
   guards (`PASS — <n> byte(s) compared` / `FAIL` / `ERROR — nothing was checked`);
   non-vacuity is absolute and a host with no `glslangValidator` is ERROR, never a pass.
   `--selftest` is fatal and runs before every scan (5 fixtures: clean pair must PASS;
   one tampered word must FAIL; **the incident itself** — GLSL divisor moved back to
   `/255u` with the blob not regenerated — must FAIL; a correct body under a tampered
   sha pin must FAIL; a zero-byte blob must ERROR). Region-scoped extraction is required
   here and not in the rect-batch guard: `spirv_blit()` is one of many blobs in its
   module, so a whole-file byte grep would splice every kernel together.
4. **Device spec added**:
   `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_blend_cpu_parity_spec.spl`
   — 6 examples, exact-value on the anchor, mirror against `color.spl` `blend()`, the
   `sa == 255` raw-store case (`0xFF020304` over the same non-opaque ground survives
   byte-exact), the `sa == 0` case, and a spatial boundary. It FAILS rather than skips
   without a Vulkan device, because `draw_image_blend`'s host fallback computes the very
   CPU `blend()` the file compares against — a skip would make every claim a tautology.
5. **Stale doc anchors corrected**: `doc/03_plan/ui/rendering/draw_ir_multibackend_plan.md`
   and `doc/05_design/ui/rendering/draw_ir_multibackend_design.md` pinned `0x101F2F3F`
   as the src-over parity anchor in 5 places. A parity gate built on that number would
   have failed every *correct* backend. Both now read `0x101E2D3C` and carry a dated
   note saying why.

## Evidence

Device, real Vulkan (MoltenVK, macOS), `SIMPLE_EXECUTION_MODE=interpreter
SIMPLE_TIMEOUT_SECONDS=0 build/cargo-r2/release/simple run`:

```
backend_vulkan_blend_cpu_parity_spec.spl     outcome=OK  executed=6  passed=6  failed=0
```

Pin guard: `PASS — 5 selftest fixture(s) checked` and
`PASS — 6848 byte(s) compared, spirv_blit() is exactly glslangValidator output for _glsl_blit()`.

Existing Vulkan lane, same binary, unchanged by this work:

```
backend_vulkan_drawing_spec                  44/44 OK
backend_vulkan_batch_and_clip_boundary_spec   7/7  OK
backend_vulkan_image_typed_upload_spec        7/7  OK
vulkan_device_submission_readback_contract    1/1  OK
```

**Two files are RED and were red before this change** — measured on pristine
`origin/main` sources with the same binary, identical failure counts, so they are
pre-existing and not caused here:
`backend_vulkan_image_exact_scratch_spec` (5/6, 1 failed) and `vulkan_resident_2d_spec`
(4/11, 7 failed). Not investigated here; recorded rather than quietly omitted.

## Sabotage — and the asymmetry that IS the bug

Restoring the old `inv` / `/255u` formula in the GLSL and **not** regenerating leaves the
device completely unaffected: all 6 examples stay green. That is not a weak spec, it is
the defect restated — a GLSL-only edit is invisible to the device. The pin guard is what
catches that case, and it does:
`FAIL — byte count differs: committed 6848, freshly compiled 6800`.

Regenerate from the sabotaged GLSL and the device goes red exactly where it should:

```
✗ blends 0x01020304 over 0x10203040 to exactly 0x101E2D3C on the device
  expected 270479167 to equal 270413116          # 0x101F2F3F vs 0x101E2D3C
✗ agrees with the frozen CPU blend() for that same pair
✓ stores an opaque source word raw ...           # sa == 255 path unaffected
✓ leaves the destination untouched for a fully transparent source
6 examples, 2 failures
```

The `sa == 255` and `sa == 0` examples staying green under sabotage is why an
exact-value oracle was needed rather than a "blending happened" smoke check. Restoring
and regenerating returns the blob to the identical sha `db0bbeb4…` (the derivation is
deterministic on this toolchain) and all 6 back to green.

A separately verified tamper: flipping one word of the committed blob makes the pin
guard FAIL (selftest fixture 2), so the guard is not merely recomputing and agreeing
with itself.

## Not fixed here, deliberately

- `src/lib/gc_async_mut/gpu/engine2d/backend_emu_math.spl:37` still names `0x101F2F3F`
  in a comment as "the parity anchor". The *code* around it was not audited by this
  lane and the file is outside its ownership; the comment is stale in the same way the
  two plan/design docs were.
- `doc/06_spec/test/02_integration/rendering/metal_engine2d_readback_spec.md` carries the
  old anchor too, but it is generated from a Metal-owned spec (F24) — fixing it there
  would be overwritten.
- Historical bug records that quote `0x101F2F3F` as the *then-current* value are history
  and are left alone.
- The rect/circle/line/gradient kernels in the same blob module are still hand-assembled
  and unpinned. Only `spirv_blit()` has a GLSL-to-blob derivation guard. Extending the
  pattern to the rest is the obvious follow-up and is not done here.
