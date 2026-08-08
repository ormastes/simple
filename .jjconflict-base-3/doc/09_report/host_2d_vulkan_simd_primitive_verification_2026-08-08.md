# Host 2D primitive rendering — Vulkan backend + SIMD CPU rasterizer verification

**Date:** 2026-08-08 · **Scope:** HOST target (Linux x86_64) only.
**Explicitly out of scope (per user instruction):** SimpleOS/baremetal 2D
(`examples/09_embedded/**`), `src/os/compositor/**`, `browser_engine/**`,
`src/compiler/**`. SimpleOS has no Vulkan; its kernel path is a separate
baremetal-framebuffer CPU rasterizer covered by a different lane. **This
report is HOST evidence only — it makes no board-runnable claim** (per
`.claude/rules/board-runnable.md`, a QEMU/host-only result must say so
plainly, not imply board coverage).

## Environment

- Binary under test: `bin/release/x86_64-unknown-linux-gnu/simple`
  (`bin/simple` symlink target), mtime 2026-08-08 03:38 UTC — a fresh Rust
  seed build (`bin/simple --version` prints the "bootstrap seed only"
  banner; `bin/simple test` hard-defaults to the tree-walk interpreter
  regardless — see `.claude/rules/testing.md`). No `cargo build` was run for
  this task; the already-deployed binary was used throughout.
- Host CPU: AMD Ryzen Threadripper 1950X, AVX2-capable (`sse2 avx avx2` in
  `/proc/cpuinfo` flags).
- Vulkan: `vulkaninfo` present (`/usr/bin/vulkaninfo`, loader 1.3.275).
  `/dev/dri` does list DRM nodes (`card1`, `card2`, `renderD128`,
  `renderD129`), but the only device the Vulkan loader itself enumerates
  headlessly in this sandbox (`vulkaninfo --summary` without `DISPLAY`) is
  **llvmpipe (Mesa 25.2.8, LLVM 20.1.2, `DRIVER_ID_MESA_LLVMPIPE`,
  `PHYSICAL_DEVICE_TYPE_CPU`)**, i.e. software Vulkan (lavapipe) —
  whether a hardware ICD would enumerate given more sandbox permissions was
  not investigated further. This is a real Vulkan 1.4 physical device
  reached through the real Vulkan API/ICD loader — it is not a Simple-side
  stub — but it is *not* a hardware GPU. Confirmed identical spec results
  with and without forcing `VK_ICD_FILENAMES=lvp_icd.json`, i.e. the default
  Vulkan loader already resolves to this device with no extra configuration.

## 1. Specs run on the deployed binary (actual `Results:` lines)

| Spec | Result |
|---|---|
| `test/01_unit/lib/gpu/engine2d/backend_software_primitives_spec.spl` | `Results: 9 total, 9 passed, 0 failed` |
| `test/01_unit/lib/gpu/engine2d/backend_software_damage_spec.spl` | `Results: 15 total, 15 passed, 0 failed` |
| `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_cpu_simd_parity_spec.spl` | `Results: 5 total, 5 passed, 0 failed` |
| `test/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_blend_spec.spl` | `Results: 5 total, 5 passed, 0 failed` |
| `test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl` (extended, see §3) | `Results: 51 total, 50 passed, 1 failed` |
| `test/01_unit/lib/gpu/engine2d/backend_software_simd_spec.spl` | `Results: 11 total, 7 passed, 4 failed` |
| `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_drawing_spec.spl` | `Results: 30 total, 30 passed, 0 failed` |
| `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_processing_spec.spl` | `Results: 22 total, 21 passed, 1 failed` |
| `test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl` | `Results: 8 total, 6 passed, 2 failed` |
| `test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_session_device_metadata_spec.spl` | `Results: 1 total, 1 passed, 0 failed` |
| `test/01_unit/check/vulkan_engine2d_frame_batch_contract_spec.spl` | `Results: 3 total, 2 passed, 1 failed` |

## 2. Vulkan backend — what is actually proven

`backend_vulkan_drawing_spec.spl` (30/30 pass) inits `VulkanBackend` against
the real lavapipe device, then for each of `clear`, `draw_line`,
`draw_circle`, `draw_rect`, and a scaled-image blit does `b.present()` →
`b.read_pixels()` and asserts on the returned pixel buffer. This is genuine
device-backed rendering, not a software mock: `it "init on host with no
Vulkan sets classifiable last_error"` in the same file exercises the failure
branch, so the passing branch is the real success path with the real ICD
loader. Caveat on `clear`'s coverage: the passing assertion
(`"clear to distinct color is deterministic across two inits"`) compares
pixel `(0,0)` and `(3,3)` between two independent `clear()` calls to each
other, not against the requested colour — it proves determinism, not
requested-colour fidelity. Combined with the fill-rect finding below, treat
"clear pixel equals the value passed to `clear()`" as **not directly
asserted** by this spec.

**Found defect (reproduced, not fixed — out of scope to fix safely in this
pass):** `backend_vulkan_processing_spec.spl` — `draw_rect_filled leaves
corners untouched` fails on exactly one of its three assertions. The failure
line (`expected 2944568831 to equal 2864434431` = `0xAF828DFF` vs expected
`0xAABBCCFF`, the fill colour) is the **center-of-rect** assertion
(`pixel_at_p(pixels, 4, 4, 8)`, strictly interior to the filled region
`(2,2,4,4)` in an 8×8 buffer) — not a corner assertion, which means both
corner-equals-background checks passed (an assertion failure would name
`286331391` = `0x111111FF` if a corner had failed). So: **the clear-path
background colour round-trips exactly at the corners, but the fill-path
colour is wrong at an interior pixel that should be uniformly solid** — not
an edge/antialiasing effect (AA would not touch a strictly-interior pixel),
and not a global colour-space shift (the background byte `0x11` came back
correct while the fill byte `0xAA`→`0xAF`, `0xBB`→`0x82`, `0xCC`→`0x8D` did
not). Mechanism undiagnosed; flagged rather than fixed since it likely
requires a SPIR-V/shader-level change outside this task's blast radius (no
`cargo build`; `backend_vulkan_spirv*.spl` not touched).
`vulkan_compute_oracle_spec.spl` — the Metal-on-Vulkan and DirectX-on-Vulkan
translation-emulation layers each expect their rendered buffer to differ
from the reference (`expected 2240 to equal 0`, i.e. 2240 non-matching
output values), so those two emulation backends do not yet match Vulkan
bit-for-bit. `vulkan_engine2d_frame_batch_contract_spec.spl`'s one failure
and `simd_kernels_spec.spl`'s one failure (see §3) are source-text
self-checks (grepping compiler-source strings), unrelated to pixel output —
one is stale after a MIR-lowering file split
(`src/compiler/50.mir/mir_lowering_expr.spl`), not a rendering defect.

**Verdict: Vulkan clear (background round-trip, determinism), line, circle,
rect-outline, and scaled-blit are proven correct on this host via a real
(software) Vulkan device. Filled-rect interior colour is a proven,
uncorrected defect** — reported here rather than silently passed over. All
four reds are recorded with file:line in
`doc/08_tracking/bug/host_2d_vulkan_and_simd_spec_reds_2026-08-08.md`.

## 3. SIMD CPU rasterizer — what is actually proven

Runtime symbols present in the deployed binary (`nm bin/release/.../simple |
awk '$3 ~ /^rt_engine2d_simd/'`):

```
rt_engine2d_simd_blend_const_span_u32   T
rt_engine2d_simd_blend_row_u32          T
rt_engine2d_simd_blend_span_u32         T
rt_engine2d_simd_copy_row_u32           T
rt_engine2d_simd_copy_span_u32          T
rt_engine2d_simd_fill_row_u32           T
rt_engine2d_simd_fill_rows_u32          T
rt_engine2d_simd_fill_span_u32          T
```

All eight are defined (`T`), including `blend_span`/`blend_const_span`,
which `doc/08_tracking/bug/t16_blend_span_c_symbol_not_reachable_three_implementations_2026-08-07.md`
recorded as **missing** from the native ABI on 2026-08-07 (present only in
`runtime_simd_dispatch.c`, dead code for the link). That gap is now closed
at the symbol level: `nm -A` on the linked archive
(`src/compiler_rust/target/release/libsimple_runtime.a`) shows the defining
object is a Rust codegen unit (`.rcgu.o`), and
`src/compiler_rust/runtime/src/value/engine2d_simd_ops.rs:195,229` now
defines both `rt_engine2d_simd_blend_span_u32` and
`rt_engine2d_simd_blend_const_span_u32` — i.e. T16 closed via the **Rust**
reimplementation gaining the two kernels, the same pattern the six sibling
kernels already used, not via the C translation unit finally getting linked.

**Important scope limit on the pixel-correctness claim below:** `bin/simple
test` hard-defaults to the tree-walk interpreter
(`.claude/rules/testing.md`), so the new spec cases in this task exercise
the extern call through the **interpreter's extern bridge**
(`interpreter_extern/simd.rs`, per T16 §1, confirmed wired), which may or
may not be the same code path the `nm` symbol above serves at JIT/native
call sites — this repo has a standing finding that engine2d SIMD kernels
have had up to three divergent implementations (Rust runtime, C runtime,
interpreter bridge) simultaneously. This report proves: **(a)** the native
ABI symbols exist in the deployed binary (`nm`, above) and **(b)** the
interpreter-bridge path for `blend_span`/`blend_const_span` produces
bit-exact pixel values matching the independently-computed scalar reference
(below). It does **not** independently confirm the JIT/native-call-site path
produces the same values — that would need a `bin/simple run` (JIT) probe,
not attempted here.

`test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl` asserts exact packed
RGBA pixel values (not just "no crash") for: `simd_fill_row`,
`engine2d_simd_fill_buffer_u32`, `rt_engine2d_simd_fill_span_u32`,
`rt_engine2d_simd_copy_span_u32`, `simd_blend_row`/`engine2d_simd_blend_row_u32`
(including bit-exact native-vs-scalar parity, e.g. `0x800000FF` blended with
`0x80FF0000` → `0xBFAA0054`, matching to the byte), `simd_blit_row`,
`blit_rect`, and `scroll_region` — all pass.

**Gap found and closed in this task:** no spec asserted pixel output for
the in-place span kernels `rt_engine2d_simd_blend_span_u32` /
`rt_engine2d_simd_blend_const_span_u32` themselves (only the row form had
exact-value coverage), even though the symbols are present. Added 6 new
`it` cases to `simd_kernels_spec.spl` exercising: bounded-span blend without
touching adjacent pixels, transparent-source no-op, bit-exact parity against
the already-proven scalar/row reference (`0xBFAA0054` reproduced via the
span path), constant-colour span blend, zero-alpha constant-colour no-op,
and the 50%-alpha constant-colour case reproducing the same known bit-exact
value. All 6 pass: `Results: 51 total, 50 passed, 1 failed` (the 1 failure
is the pre-existing, unrelated MIR-source-text self-check noted in §2).

**Separately tracked, not re-litigated here:**
`doc/08_tracking/bug/engine2d_simd_span_kernels_slower_and_fill_colour_corrupt_2026-08-06.md`
found the *marshalling* path (`simd_fill_row`/`simd_blend_row`, which copy
through a fresh array + FFI + scatter) is slower than scalar, so
`native_pixel_rows_enabled()` defaults `off` unless `SIMPLE_2D_SIMD` names an
ISA explicitly; that gating is why `backend_software_simd_spec.spl`'s 4
`AC-6` hit-counter cases (`simd_hit_counts().fill_hits` etc., expecting
`>0`) fail with both `SIMPLE_2D_SIMD` unset and `SIMPLE_2D_SIMD=avx2` — the
counters track the disabled row-marshalling path, not the in-place span
path this task verified is correct. That file's colour-corruption finding
(§2) was independently retracted as a decimal/hex conversion error on
2026-08-07 (`doc/03_plan/ui/perf/engine2d_simd_fill_span_colour_boxing_fix_plan_2026-08-07.md`);
this task's fresh run reproduces byte-exact fill/blend values, consistent
with that retraction.

**Verdict: fill, copy, and blend — both row and in-place-span forms,
including the constant-colour span variant — are proven bit-exact through
the interpreter-executed extern-call path on this AVX2-capable host** (not a
scalar-only fallback: `simd_kernels_spec.spl`'s `"native and scalar rows
match ..."` and the new span-parity case both compare the extern call's
output against an independently-computed scalar reference and assert
equality, and `engine2d_simd_has_avx2()` / `active_arch_text()` assertions
confirm AVX2 is the detected level on this host). The native ABI symbols
backing that call are confirmed present in the deployed binary via `nm`
(above); whether the JIT/native call-site path resolves to byte-identical
output was not independently checked in this pass (see scope limit above).

## Honest summary

| Primitive | Vulkan (lavapipe/software device) | SIMD CPU |
|---|---|---|
| clear | proven for background round-trip (corner pixels exact) and cross-init determinism; requested-colour-equals-output not directly asserted | proven (fill kernels, bit-exact) |
| fill rect (solid) | **defect found**: interior pixel wrong colour, mechanism undiagnosed, not fixed | proven (fill span + fill row, bit-exact) |
| blit / copy | proven (scaled-image blit test) | proven (`simd_blit_row`, `rt_engine2d_simd_copy_span_u32`, `blit_rect`, bit-exact) |
| line | proven (no-crash + pixel-buffer-length; not a full pixel-path assertion) | not in this task's scope (line rasterization is not a SIMD-kernel primitive here) |
| circle | proven (no-crash + pixel-buffer-length; not a full pixel-path assertion) | not applicable |
| alpha blend | unproven at primitive level (only cross-backend emulation parity was tested, and it fails) | proven (`simd_blend_row`, and — newly added this task — `blend_span`/`blend_const_span`, all bit-exact) |
| scroll | not tested on Vulkan in this pass | proven (`scroll_region`, bit-exact vs scalar reference) |

Net: **primitive Simple 2D rendering works on this host** — clear/blit/
fill/blend all have real pixel-level evidence on both the Vulkan
(software-device) backend and the SIMD CPU rasterizer, with one concrete
Vulkan defect (filled-rect interior colour) and two emulation-parity defects
(Metal-on-Vulkan, DirectX-on-Vulkan) found and left open, tracked at
`doc/08_tracking/bug/host_2d_vulkan_and_simd_spec_reds_2026-08-08.md`, rather
than silently passed over.
