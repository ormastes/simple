# Vulkan font lane: whole-atlas SHA-256 costs ~10 min per atlas upload

- **Filed:** 2026-08-04
- **Status:** FIXED (this change)
- **Site:** `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl` (was line 360)
- **Impact:** every spec touching vector-font rendering on the vulkan lane was
  effectively unverifiable; it dominated two separate investigation lanes.

## Symptom

A two-glyph draw on the vulkan font lane burned tens of minutes of CPU. The
cost showed up as `evidence_overhead_ns`, not as render time.

## Root cause

```
self.font_atlas_payload_sha256 = sha256_u8_hex(atlas_payload)
```

The font atlas is a **fixed 1024x1024** — `FONT_ATLAS_WIDTH` /
`FONT_ATLAS_HEIGHT` in `src/lib/nogc_sync_mut/text_layout/font_renderer.spl:464-465`
— regardless of how many glyphs the batch actually draws. So even a two-glyph
draw hashed `1024 * 1024 * 4 = 4,194,304` bytes.

The vulkan font lane runs **interpreted**: the `vulkan_sffi_*` externs are
unresolved in the JIT, and an unresolved external symbol drops the *whole
module* to the interpreter (`[jit-fallback] ... whole module dropped to the
interpreter`). Interpreted `sha256_u8_hex` measures **~7.2 KB/s**.

This is the same class of defect already documented for font *asset* loading in
`src/lib/common/encoding/font_registry.spl:566-575` and
`doc/08_tracking/bug/engine2d_load_font_interpreter_3kb_per_sec_2026-07-25.md`.
It is not an inefficiency in the SHA-256 code — 64-byte blocks of interpreted
bit-twiddling simply cost ~23 ms each.

Note the call was already correctly gated behind the atlas dirty check
(`font_atlas_generation` / `font_atlas_owner_identity`), so it ran once per
atlas mutation, not once per quad. The problem is that the *cold* cost alone is
~10 minutes, and every fresh render pays it once.

## Measurements (external, `/usr/bin/time`; never in-language)

Interpreted (`SIMPLE_EXECUTION_MODE=interpret`), replicating the exact hot path
(1024x1024 `[u32]` atlas -> `_vulkan_font_pixels_to_bytes` -> digest):

| step | wall |
|---|---|
| convert only (4 MB) — unavoidable, feeds the upload | **11.36 s** |
| convert + old whole-atlas `sha256_u8_hex` | **635.85 s** |
| => old hash step alone | **624.5 s** (98.2% of the path) |
| convert + new digest | **~14.8 s** |
| => new digest step alone | **~3.4 s** |

Primitive rate check confirming linearity of the old path: 16 KB = 2.29 s,
32 KB = 4.26 s => ~7.2 KB/s; extrapolating to 4,194,304 B predicts ~580 s,
consistent with the measured 624.5 s.

**Atlas-upload path: 635.85 s -> ~14.8 s (~43x). Digest step: ~180x.**

## What the token actually guarantees

Audited across every consumer in `src/`, `test/`, `scripts/` and `doc/` before
changing anything. It is a **change-detection token with a well-formedness
gate** — *not* a cryptographic or parity checksum:

- **Shape:** `vulkan_font_stage_evidence_ready` requires `.len() == 64`
  (`backend_vulkan_font.spl`); the live-evidence checker requires 64 lowercase
  hex chars (`scripts/check/check-macos-gpu-2d-live-evidence.shs` `sha256_valid`,
  `test/02_integration/rendering/macos_gpu_2d_live_harness.spl:120`).
- **Change detection:** the only value comparisons are warm-vs-cold equality
  *within one receipt* (`macos_gpu_2d_live_harness.spl:500`,
  `check-macos-gpu-2d-live-evidence.shs:875-876`) and stability across samples
  (`test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl:490,494`).
- **NOT security, NOT cross-process parity:** no consumer anywhere recomputes
  this digest independently and compares values, and no 64-hex constant pins
  the engine2d atlas payload. The digest is written into receipts, but the
  checker only validates hex shape and warm==cold within the same receipt.

The one recompute-and-compare in the tree —
`test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl:415`,
`native.atlas_payload_sha256 == sha256_u8_hex(evidence_alpha)` — belongs to the
**engine3d** adapter's alpha-channel digest
(`src/lib/gc_async_mut/gpu/engine3d/vulkan_font_adapter.spl:174`), a different
writer over different bytes. **It was deliberately left untouched.** The
engine2d evidence class in that same spec has no `atlas_payload_sha256` field
at all.

## Fix

`_vulkan_font_atlas_payload_digest(pixels, width, height)` in
`backend_vulkan_font.spl`. Still a **real SHA-256** producing the identical
64-char lowercase hex shape, but it is no longer fed 4 MB: every pixel is folded
into a 128-bit four-lane fingerprint (unrolled by 4, no per-element branch),
and SHA-256 is then taken over that fingerprint plus atlas geometry
(`len`, `width`, `height`).

Coverage is unchanged — **all 1024x1024 pixels still contribute**, so any atlas
mutation still moves the token — and the element index is mixed into each lane
so position matters.

Verified sensitivity (interpreted, full 1024x1024 atlas):

| property | result |
|---|---|
| determinism (rebuild identical atlas) | equal |
| single pixel changed | differs |
| two pixels swapped (same multiset) | differs |
| one pixel shifted by 1 index (crosses lane) | differs |
| output shape `.len() == 64` lowercase hex | true |

Rendered output is unaffected by construction: the change touches only the
evidence token. `atlas_payload = _vulkan_font_pixels_to_bytes(batch.atlas_pixels)`
is still built and still uploaded byte-for-byte via `vulkan_sffi_copy_to_buffer`;
no pixel, quad, dispatch or readback path was modified. Diff is +79/-1 in one
file.

## Why not the other options

- **Cache / dirty flag:** already present and already correct. It does not help,
  because the *cold* cost is the problem.
- **Hash only the dirty rect:** would silently stop detecting changes elsewhere
  in the atlas — exactly the "slow guarantee traded for a silent one" failure
  this repo has been fighting.
- **Route to a native SHA-256:** would preserve the digest value exactly and is
  the ideal fix, but **no byte-buffer digest extern is registered for the
  interpreter**. `rt_file_hash_sha256` / `rt_package_sha256` take a *path*;
  `rt_sha256_new/write/finish` exist natively
  (`src/compiler_rust/runtime/src/value/sffi/hash/sha256.rs`) but are AOT-only,
  absent from `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`.
  Wiring one up spans ~7 Rust-seed files and needs a bootstrap rebuild — a
  separate lane, and against the standing "fix .spl not Rust" rule.
  **Follow-up:** registering `rt_sha256_*` for the interpreter would let this
  site (and `font_registry`, and the engine3d adapter) return to a plain
  full-buffer SHA-256 at native speed.

## Provenance

Measured in the shared working copy at `9dcd16644b8`, **76 commits behind
origin** (`5b4f0b478007975193c863225c387c1ebf4eb61f`). Origin tip does **not
compile** — unrelated `translate_call` trait break, filed at
`doc/08_tracking/bug/mir_to_llvm_translate_call_trait_break_2026-08-04.md` — so
the shared WC is the only testable base. The WC copy of
`backend_vulkan_font.spl` was verified **byte-identical to origin tip** before
editing, so this change applies cleanly to current origin content.
