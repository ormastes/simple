# 2D Rendering → Vulkan: Functional + Optimization Verification & Coverage Plan (2026-08-07)

Deep plan for functional correctness, honest optimization verification, and near-100%
function/branch coverage of the 2D rendering stack, from the compositor-backend
interface DOWN through engine2d, render_opt, SIMD kernels, and the Vulkan-least lane.
All executable units are container-headless. Written at single-agent (Sonnet/Haiku)
granularity: exact files, named `it` blocks, copy-pasteable commands, sabotage recipes,
done checklists, collision sets. No deferred design decisions.

## Scope boundary (coordinated with sibling plan)

A sibling plan (`doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md`)
covers WM/GUI/web-HTML-CSS system tests ABOVE the compositor-backend interface.
**This plan covers everything BELOW that interface:**

- `src/lib/common/gpu/engine2d/` — `scalar_oracle.spl`, `kernel_registry.spl`
- `src/lib/nogc_sync_mut/gpu/engine2d/` — `simd_isa_provider.spl`, `simd_kernels.spl`,
  `simd_native_rows.spl`, `simd_provider.spl`, sessions, ffi/sffi shims
- `src/lib/gc_async_mut/gpu/engine2d/` — backends (software, vulkan, virtio-gpu, ...),
  draw_ir, bridges, sessions
- `src/lib/common/ui/render_opt/` — `property_trees.spl`, `revisions.spl`,
  `paint_chunk_rasterizer.spl`, `draw_ir_delta.spl`
- `src/os/compositor/` — `compositor_engine2d.spl`, `engine2d_baremetal_core.spl`,
  `engine2d_baremetal_rect_core.spl`, `vulkan_compositor_backend.spl`,
  `display_backend_core.spl` (trait), software/fb paths
- `src/os/drivers/virtio/virtio_gpu_capset.spl` (+ types/init) — Vulkan-least protocol lane

Do NOT add tests for `wm_core`, `wm_scene`, window decorations, layout_manager, web/HTML
paths — those belong to the sibling. Collision risk with the sibling is limited to
`test/01_unit/os/compositor/` (shared directory, disjoint files) — every unit below
lists its exact file set; never edit a file outside your unit's set.

## Investigation findings (baseline reality, verified 2026-08-07)

1. **Existing test surface** is large (~140 engine2d specs, ~90 compositor specs across
   `test/01_unit/`, `test/02_integration/rendering/`, `test/03_system/`). Landed
   patterns to replicate exactly:
   - `test/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.spl` — canonical pinned
     hashes (`oracle_hash_span` over fixed pseudo-random spans).
   - `test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_isa_provider_spec.spl` —
     bit-exact vs scalar oracle + honest timing gates; `slow_it` for ~200s cases.
   - `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_software_kernel_table_bucket_spec.spl`
     — bucket-table dispatch proof.
   - `test/01_unit/os/compositor/engine2d_damage_report_spec.spl` — damage accounting.
   - `test/01_unit/os/compositor/vulkan_compositor_backend_spec.spl` (10 its) — honest
     gating: `is_available()==false`, reject-counting per op.
   - `test/01_unit/lib/common/ui/render_opt/paint_chunk_rasterizer_spec.spl`,
     `draw_ir_delta_spec.spl` — proportionality via count assertions.
   - `test/01_unit/os/drivers/virtio/virtio_gpu_capset_spec.spl` (36 its) — the WS-E
     capset opcode lane already landed; extend, don't duplicate.
2. **Vulkan reality**: `src/os/compositor/vulkan_compositor_backend.spl` is honestly
   gated OFF — `is_available()` hardcoded `false` (virtio-gpu is QEMU-only; board gap
   filed per `.claude/rules/board-runnable.md`). Every `CompositorBackend` trait method
   (`width`, `height`, `clear`, `fill_rect`, `draw_text`, `draw_char_8x16`, `put_pixel`,
   `blit_pixels`, `present`, `present_rect`, `as_glass_capable`) routes through
   `self.reject(op)`. **"Functional check with vulkan least" therefore CANNOT mean real
   GPU execution in a container.** The honest headless-testable Vulkan surface is:
   (a) trait conformance + reject-path accounting, (b) virtio-gpu capset/protocol
   encode/decode logic (pure CPU), (c) a QEMU virtio-gpu smoke lane (QEMU already runs
   headless here via `-display none`, see `scripts/os/run_simpleos_q35_smoke.shs:90`).
   Real-GPU/board execution is BLOCKED-ON-HARDWARE (Wave 4, unit V4).
3. **"Fully optimized" honest finding**: under the interpreter engine, SIMD-ISA loses
   to scalar at every measured bucket; `kernel_registry`'s gate correctly keeps scalar
   registered. Optimization units are therefore ENGINE-AWARE: always pin bit-exactness;
   measure and RECORD per-engine timing (interpreter via `bin/simple test`, JIT via
   `bin/simple run` — different engines, see `.claude/rules/testing.md`); assert the
   honest-gate invariant (registered ⟺ measured faster), never assert "SIMD wins".
   All current numbers are interpreter-only; Wave 1 adds the JIT lane.
4. **Coverage tooling exists**: `src/app/spl_coverage/main.spl` — branch/decision
   coverage for `.spl` files. Enable with `SIMPLE_COVERAGE=1` during test runs; then
   `bin/simple spl-coverage dump > coverage.sdn` / `status` / `clear`. Function-level
   and per-module rollup granularity must be VERIFIED (and extended if absent) by unit
   B1 before any percentage target is enforced.
5. **Container**: there is NO `scripts/local-container-test.shs` in the tree (checked
   2026-08-07). Container lane = plain podman/docker mount (recipe below). Every
   engine2d/render_opt/compositor unit in this plan is pure-CPU and needs no display,
   GPU, or network. The QEMU smoke unit needs `/dev/kvm` passthrough or falls back to
   TCG (slower, still headless) — explicitly feasible in-container with `-display none`.

### Container recipe (used by every unit)

```bash
# One-time image: any glibc linux with make/gcc absent is fine; the repo binary is static enough.
podman run --rm -v /home/ormastes/dev/pub/simple:/w -w /w docker.io/library/debian:bookworm \
  sh -c 'bin/release/x86_64-unknown-linux-gnu/simple test <SPEC> --no-cache --no-cover-check'
# KVM variant for the QEMU unit only:
podman run --rm --device /dev/kvm -v /home/ormastes/dev/pub/simple:/w -w /w <image> sh -c '<qemu check script>'
```

Notes: `--no-cache --no-cover-check` is mandatory (concurrent runs race the shared
manifest). Verify binary provenance first: `readlink -f bin/simple` must resolve to
`bin/release/x86_64-unknown-linux-gnu/simple`; run `--version` + a positive capability
probe (a subcommand only the current build has) — size and banner both lie.

## Standing conventions (apply to EVERY unit)

1. **Sabotage-test**: before trusting a new spec green, break the implementation (not a
   shim — sabotage the real function body), confirm the spec goes red, revert. Record
   the sabotage line in the unit log. Bare `assert` is INERT in sspec — use matchers.
2. **Binary provenance**: `readlink -f bin/simple`; never trust a stale scratch build.
3. **Engines**: `bin/simple test` = interpreter/seed lane; `bin/simple run` = JIT.
   `SIMPLE_EXECUTION_MODE=native` is NOT a mode. JIT refuses modules containing lambdas.
4. **`slow_it`** for any case that can exceed 120s (daemon honors it as of this week).
5. **Test-DB writes are sequential** — do not run two `bin/simple test` invocations
   concurrently against the shared DB; use `--no-cache --no-cover-check` in containers.
6. **No `Dict.len()` / no `.get()` on struct-valued dicts** under native codegen.
7. **Landing**: shared-tree plumbing landing (fixed index path per unit, listed below),
   3 push guards (`check-no-conflict-tree-push`, `check-no-conflict-markers-push`,
   `check-tree-size-push`), push over SSH, verify with `ls-remote`. Full recipe at end.
8. **Spec style**: mirror `test/` path to source path; `describe`/`it` with matchers;
   import pattern per `.claude/rules/testing.md`; no `fn main` in spec files (it drops
   every describe block).

---

## Wave 1 — Baseline (3 units, no dependencies, run in parallel)

### Unit B1 — Coverage measurement bring-up + per-module baseline
- **Files**: read `src/app/spl_coverage/main.spl`; create
  `scripts/check/check-render2d-coverage.shs`; report table goes into
  `doc/09_report/ui/testing/render2d_coverage_baseline_2026-08-07.md` (NOT committed
  unless requested — repo rule; keep in PR only if user asks).
- **Steps**:
  1. `SIMPLE_COVERAGE=1 bin/simple test test/01_unit/lib/common/gpu/engine2d/ --no-cache --no-cover-check`
     then `bin/simple spl-coverage dump > /tmp/claude-1000/render2d_cov.sdn` and `status`.
  2. Verify the dump distinguishes (a) function hit/miss and (b) branch/decision arms
     per `.spl` file. If either is missing, extend `src/app/spl_coverage/main.spl` with
     a `report --filter <path-prefix>` subcommand that rolls up per-file
     `functions_hit/functions_total` and `branches_hit/branches_total`. That extension
     is IN SCOPE for this unit and must itself get a spec:
     `test/01_unit/app/spl_coverage/spl_coverage_report_filter_spec.spl` with its:
     `it "report --filter narrows to prefix"`, `it "reports function and branch totals per file"`,
     `it "empty filter matches nothing and says so"` .
  3. Record baseline numbers for each module group: `src/lib/common/gpu/engine2d`,
     `src/lib/common/ui/render_opt`, `src/lib/nogc_sync_mut/gpu/engine2d`,
     `src/os/compositor` (engine2d+vulkan files only), `src/os/drivers/virtio` (gpu files).
- **Sabotage**: mark one known-covered function as uncovered by clearing
  (`spl-coverage clear`) and re-running only an unrelated spec — the report must show
  the drop; if it stays green the measurement is fail-open, STOP and fix.
- **Container**: recipe above with `SIMPLE_COVERAGE=1` inside the `sh -c`.
- **Done**: dump parses; function+branch granularity confirmed or built; baseline table
  exists with real numbers; sabotage red observed.
- **Collision set**: `src/app/spl_coverage/**`, `scripts/check/check-render2d-coverage.shs`.

### Unit B2 — JIT-engine timing baseline for SIMD kernels
- **Files**: create `scripts/check/check-engine2d-jit-timing.shs` and harness
  `src/app/test/engine2d_jit_timing_probe.spl` (a `bin/simple run` entrypoint; keep it
  lambda-free — JIT refuses lambdas).
- **Steps**: for buckets {64, 256, 1024, 4096, 16384} px, time
  `oracle_fill_const` vs `simd_isa_fill_const`, `oracle_src_over` vs
  `simd_isa_blend_span`, `oracle_copy_span` vs SIMD copy, under BOTH engines:
  `bin/simple run src/app/test/engine2d_jit_timing_probe.spl` (JIT) and
  `SIMPLE_EXECUTION_MODE=interpret bin/simple run ...` (interpreter). Print a
  machine-parseable line per (kernel, bucket, engine): `TIMING kernel=<k> bucket=<b> engine=<e> scalar_ns=<n> simd_ns=<n>`.
- **Assertions (in spec `test/05_perf/rendering/engine2d_jit_timing_receipt_spec.spl`)**:
  (a) bit-exact: `oracle_hash_span` of SIMD output == scalar output for every bucket —
  hard fail; (b) timing lines present for both engines — hard fail; (c) NO assertion
  that SIMD is faster; instead assert the honest-gate invariant: for each bucket,
  `kernel_table_lookup` returns the SIMD kernel ⟺ recorded simd_ns < scalar_ns on the
  engine the table was sealed under. its: `it "simd output bit-exact vs scalar oracle on all buckets"`,
  `it "emits timing receipt for interpreter and jit engines"`,
  `it "kernel_registry registration matches measured winner (honest gate)"`.
  Use `slow_it` for the full-bucket sweep.
- **Sabotage**: flip one registered kernel in `kernel_table_register` to the loser —
  honest-gate `it` must go red.
- **Container**: pure CPU; recipe above.
- **Done**: receipts for both engines recorded (this is the FIRST JIT number for this
  stack — all prior numbers were interpreter-only); honest-gate spec green; sabotage red.
- **Collision set**: `scripts/check/check-engine2d-jit-timing.shs`,
  `src/app/test/engine2d_jit_timing_probe.spl`, the new perf spec.
- **Depends**: none (B1 not required).

### Unit B3 — Container-run verification of the existing 2D suite
- **Files**: none created except a log; optionally `scripts/check/check-render2d-container-suite.shs`
  wrapping the list below.
- **Spec list (expected green, run each in-container)**:
  `test/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.spl`,
  `test/01_unit/lib/common/ui/render_opt/{draw_ir_delta,paint_chunk_rasterizer,render_opt_invalidation}_spec.spl`,
  `test/01_unit/lib/nogc_sync_mut/gpu/engine2d/{simd_isa_provider,simd_span_batch_execute}_spec.spl`,
  `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_software_kernel_table_bucket_spec.spl`,
  `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_software_rounded_rect_spec.spl`,
  `test/01_unit/os/compositor/{engine2d_damage_report,engine2d_compositor_revision_cache,engine2d_render_evidence,engine2d_baremetal_core_parity,vulkan_compositor_backend}_spec.spl`,
  `test/01_unit/os/drivers/virtio/virtio_gpu_capset_spec.spl`.
- **Done**: every listed spec green in-container with `--no-cache --no-cover-check`;
  any red is triaged as environment vs product and filed before Wave 2 starts.
- **Collision set**: read-only (script file only). **Depends**: none.

---

## Wave 2 — Functional closure (public functions without specs)

Each unit begins with the inventory-verify step (functions may have gained coverage
since 2026-08-07): `grep -o "fn [a-z_0-9]*" <src file> | sort -u` then grep the paired
spec for each name; test only the still-missing ones. Function lists below are the
verified 2026-08-07 inventory. Each unit: one new or extended spec file, oracle-hash or
pixel-diff assertions in the landed style, sabotage per new `it`.

### Unit F1 — kernel_registry completion
- **Src**: `src/lib/common/gpu/engine2d/kernel_registry.spl`. **Spec**: extend
  `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_software_kernel_table_bucket_spec.spl`
  or create `test/01_unit/lib/common/gpu/engine2d/kernel_registry_spec.spl` (create —
  mirror path is cleaner; leave the bucket spec untouched).
- **Functions**: `kernel_slot_key`, `kernel_size_bucket` (edge px counts 0/1/63/64/65...),
  `kernel_table_new/register/lookup/seal`, `span_batch_new/push/reset/execute`.
- **its**: `it "kernel_size_bucket maps boundary pixel counts to stable buckets"`,
  `it "kernel_slot_key is injective across op/bucket pairs"`,
  `it "register-after-seal is rejected and lookup unchanged"`,
  `it "lookup miss falls back to scalar, never nil"`,
  `it "span_batch_reset empties and allows reuse without realloc growth"`.
- **Sabotage**: make `kernel_table_seal` a no-op → seal `it` red.
- **Done**: all its green in-container; sabotage red; B1 coverage for this file rises.

### Unit F2 — scalar_oracle clip family + hash pinning
- **Src**: `src/lib/common/gpu/engine2d/scalar_oracle.spl`. **Spec**: extend
  `test/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.spl`.
- **Functions**: `oracle_clip_count/offset/pack/span/span_pair/paired_src`,
  `oracle_mask_src_over`, `oracle_modulate_alpha`, `oracle_src_over_image`,
  channel extractors `oracle_red/green/blue/alpha` + `oracle_pack` roundtrip.
- **its**: `it "clip pack/unpack roundtrips count and offset"`,
  `it "clip_span degenerate: zero-width, full-width, off-left, off-right"`,
  `it "mask_src_over with mask=0 is identity and mask=255 equals src_over (pinned hash)"`,
  `it "modulate_alpha 0 and 255 endpoints pinned"`,
  `it "src_over_image pinned hash on 64px pseudo-random span"`,
  `it "pack(red,green,blue,alpha) roundtrips channel extractors"`.
  Pin hashes by computing once, printing, then hard-coding — the landed
  scalar_oracle_spec pattern. Never fabricate a hash (fabricated-KAT trap).
- **Sabotage**: swap red/blue in `oracle_pack` → roundtrip + pinned-hash its red.

### Unit F3 — render_opt property_trees + revisions
- **Src**: `src/lib/common/ui/render_opt/property_trees.spl`, `revisions.spl`.
- **Spec**: create `test/01_unit/lib/common/ui/render_opt/property_trees_revisions_spec.spl`
  (do NOT edit `render_opt_invalidation_spec.spl` — it belongs to landed work; check its
  18 its for overlap first).
- **Functions**: `paint_chunks_property_rev`, `paint_chunks_raster`, `paint_chunks_sync`,
  `revisions_mark`, `revisions_chunk_grouping_rev`, both `create`s.
- **its**: `it "property_rev unchanged input produces identical rev (idempotent)"`,
  `it "single node mutation bumps only affected chunk revs (count assertion)"`,
  `it "paint_chunks_sync raster count proportional to dirty chunks not total"`,
  `it "revisions_mark is monotonic and never reuses a rev"`,
  `it "chunk_grouping_rev stable under reorder of unrelated nodes"`.
- **Sabotage**: make `revisions_mark` return a constant → monotonic `it` red.

### Unit F4 — paint_chunk_rasterizer + draw_ir_delta edge closure
- **Src**: `src/lib/common/ui/render_opt/paint_chunk_rasterizer.spl`, `draw_ir_delta.spl`.
- **Spec**: extend both existing specs
  (`paint_chunk_rasterizer_spec.spl`, `draw_ir_delta_spec.spl`).
- **Functions/edges**: `paint_rect` (clip to chunk bounds, zero-area, negative origin),
  `paint_chunk_rasterizer_run` (empty chunk list), `draw_ir_delta_build` (identical
  frames → empty delta), `draw_ir_delta_replay` (replay(delta(a,b)) over a == b, by
  oracle hash of rasterized output).
- **its**: `it "paint_rect clips to chunk bounds (oracle hash)"`,
  `it "zero-area and negative-origin rects paint nothing"`,
  `it "delta of identical frames is empty (count==0)"`,
  `it "replaying delta reconstructs target frame bit-exact (oracle hash)"`.
- **Sabotage**: off-by-one the clip in `paint_rect` → hash `it` red.

### Unit F5 — simd_provider registration/accounting
- **Src**: `src/lib/nogc_sync_mut/gpu/engine2d/simd_provider.spl`.
- **Spec**: create `test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_provider_spec.spl`.
- **Functions**: `register_simd_provider`, `has_registered_provider`,
  `registered_provider_name`, `reset_simd_hits`, `simd_hit_counts`,
  `record_simd_{fill,copy,alpha,blit,scroll}_hit`, `record_simd_vectorize_change`,
  `make_simd_hit_counts_zero`, `target_features`.
- **its**: `it "no provider registered reports absent with empty name"`,
  `it "register then query returns name and true"`,
  `it "each record_*_hit increments exactly its counter"`,
  `it "reset zeroes all counters"`,
  `it "vectorize_change events are counted separately from hits"`.
- **Sabotage**: cross-wire fill hit to copy counter → per-counter `it` red.

### Unit F6 — simd_kernels dispatch + evidence surface
- **Src**: `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl` (largest gap).
- **Spec**: extend `test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl` — verify first
  which of these are already covered there.
- **Functions**: `scroll_region` (+`_scalar_scroll_region` parity), `blit_rect`
  (+`_scalar_blit_rect` parity, overlapping src/dst), `detect_simd_level`,
  `simd_config_mode` (env-driven branches), `diagnostic_text`/`arch_text`/`feature_text`
  (non-empty, mentions detected level), `cpu_simd_runtime_evidence` +
  `cpu_simd_required_evidence_valid` (evidence honesty), `executed_all`, `hit_counts`,
  `native_pixel_rows_enabled`.
- **its**: `it "scroll_region up/down/left/right parity vs scalar (oracle hash)"`,
  `it "blit_rect overlapping regions parity vs scalar"`,
  `it "detect_simd_level returns a level consistent with has_sse/avx2/neon/rvv probes"`,
  `it "simd_config_mode honors env override and defaults honestly"`,
  `it "runtime evidence is valid iff kernels actually executed (executed_all)"`,
  `it "diagnostic_text names active arch and features"`.
- **Sabotage**: make `cpu_simd_runtime_evidence` return canned success without
  execution → evidence `it` red (fabricated-stub guard pattern: never accept an
  absence condition as proof).

### Unit F7 — simd_native_rows wrapper parity
- **Src**: `src/lib/nogc_sync_mut/gpu/engine2d/simd_native_rows.spl`.
- **Spec**: create `test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_native_rows_spec.spl`.
- **Functions**: `engine2d_simd_{fill_row,fill_rows,fill_buffer,copy_row,blend_row,blend_span,blend_const_span}_u32`,
  `engine2d_simd_native_hits/reset`. NOTE `[u32]` is NOT a packed buffer (8-byte
  stride) — build expected values through the scalar oracle on the same representation,
  never by raw byte math.
- **its**: `it "fill_row_u32 matches oracle_fill_const per element"`,
  `it "blend_span_u32 matches oracle_src_over (pinned hash)"`,
  `it "blend_const_span_u32 matches oracle_src_over_const"`,
  `it "native_hits increments when native path taken and reset zeroes"`,
  `it "wrappers fall back safely when native rows disabled (native_pixel_rows_enabled=false path)"`.
- **Sabotage**: invert alpha in the blend wrapper's fallback → hash red.

### Unit F8 — compositor_engine2d surface completion
- **Src**: `src/os/compositor/compositor_engine2d.spl`.
- **Spec**: create `test/01_unit/os/compositor/compositor_engine2d_surface_spec.spl`
  (revision-cache behavior already lives in `engine2d_compositor_revision_cache_spec.spl`
  — do not duplicate; test only the untested remainder).
- **Functions**: `create/create_named/create_from_env`, `selected_backend`,
  `set_pixel_buffer_override` + `retained_pixel_buffer_override_count` +
  `get_pixel_buffer`, `invalidate_frame_receipt`, `invalidate_revision_cache` (only the
  arm not covered by the revision-cache spec), `font_provenance`, `frame_provenance`,
  `host_wm_render_backend_key`, env override arms
  (`_engine2d_compositor_gpu_backend`, `_engine2d_compositor_clear_override`,
  `_engine2d_compositor_transfer_profile`).
- **its**: `it "create_from_env honors backend env override and falls back to software"`,
  `it "pixel buffer override is retained, counted, and returned by get_pixel_buffer"`,
  `it "invalidate_frame_receipt forces next frame_provenance to change"`,
  `it "font and frame provenance name the actual backend (no fabricated provenance)"`,
  `it "host_wm_render_backend_key stable across frames on same backend"`.
- **Sabotage**: hardcode `frame_provenance` → provenance `it` red.
- **Collision caution**: shared dir with sibling plan; file set here is exactly this
  one new spec + no source edits.

### Unit F9 — engine2d baremetal + software primitives gap
- **Src**: `src/os/compositor/engine2d_baremetal_core.spl`,
  `engine2d_baremetal_rect_core.spl`.
- **Spec**: extend `test/01_unit/os/compositor/engine2d_baremetal_core_parity_spec.spl`.
- **Step 1** enumerate: `grep -o "fn [a-z_0-9]*" src/os/compositor/engine2d_baremetal_core.spl src/os/compositor/engine2d_baremetal_rect_core.spl | sort -u`
  and diff against the parity spec's covered names; write one `it` per missing public fn.
- **Pattern**: every `it` asserts baremetal-core output == gc-tier software backend
  output via `oracle_hash_span` over the framebuffer (the landed parity pattern).
- **Sabotage**: nudge one rect edge in `engine2d_baremetal_rect_core` → parity red.

Wave 2 units are mutually independent; all depend on B3 (suite verified green).

---

## Wave 3 — Branch coverage closure (~100% with honest exclusions)

Acceptance for every unit: the B1 measurement command, before/after numbers recorded.
Target: **100% function coverage; ≥95% branch coverage per module**, with a named
exclusion list — each exclusion justified in the spec file header comment.

**Honest exclusions (pre-approved):**
- FFI/SFFI-only arms (`ffi_*.spl`, `sffi_*.spl`, `rt_*` extern shims) — reachable only
  with real drivers; covered by contract specs asserting the reject/absent path.
- Platform arms not compilable on linux-x86_64 (metal/cocoa/win32/neon-on-x86).
- `VulkanCompositorBackend.is_available()` false-arm's TRUE branch — proven by the
  existing sabotage-style live-flip test (flip to true, observe specs notice, revert);
  do not add a fake runtime path to cover it.

### Unit C1 — `src/lib/common/` closure (engine2d + render_opt)
Command (acceptance):
```bash
bin/simple spl-coverage clear
SIMPLE_COVERAGE=1 bin/simple test test/01_unit/lib/common/ --no-cache --no-cover-check
bin/simple spl-coverage dump | <B1 report filter> src/lib/common/gpu/engine2d src/lib/common/ui/render_opt
```
Close remaining arms (typically: clip degenerate branches, seal/reject arms, empty-input
early returns). One `it` per uncovered branch, named after the branch:
`it "covers <fn> <condition> arm"` is acceptable naming for pure closure its.

### Unit C2 — `src/lib/nogc_sync_mut/gpu/engine2d/` closure
Focus: `simd_kernels.spl` env/feature-detect branch matrix (`SIMPLE_SIMD*` env values ×
detected level), `simd_isa_provider.spl` per-kernel dispatch arms,
`kernel_registry` bucket boundaries. Feature-detect arms that require absent hardware
(neon/rvv on x86) go to the exclusion list with the platform justification.

### Unit C3 — `src/os/compositor/` engine2d+software+vulkan closure
Focus files: `compositor_engine2d.spl`, `engine2d_baremetal_*.spl`,
`vulkan_compositor_backend.spl`, `display_backend_core.spl`, `dirty_rect.spl`,
`frame_pacer.spl` (only if the sibling plan's inventory hasn't claimed it — check
its collision list before starting; if claimed, drop it here).
Acceptance command as C1 with the os/compositor filter and the unit-test path
`test/01_unit/os/compositor/`.

Wave 3 depends on B1 (measurement) and the corresponding Wave 2 unit per module.

---

## Wave 4 — Vulkan-least lane

### Unit V1 — VulkanCompositorBackend full trait conformance via reject path
- **Src**: `src/os/compositor/vulkan_compositor_backend.spl` (read-only).
- **Spec**: extend `test/01_unit/os/compositor/vulkan_compositor_backend_spec.spl`
  (currently 10 its) to exercise EVERY trait method:
  `clear`, `fill_rect`, `draw_text`, `draw_char_8x16`, `put_pixel`, `blit_pixels`,
  `present`, `present_rect`, `width`, `height`, `as_glass_capable`, plus
  `create_from_env`, `create_with_render_node`, `unavailable_reason`,
  `detect_virtio_gpu_device` (nonexistent node → false; a plain file → false).
- **its**: `it "every drawing op is rejected exactly once per call (count delta per op)"`,
  `it "last_rejection names the most recent op in call order"`,
  `it "width/height report constructed dimensions without rejection"`,
  `it "as_glass_capable is nil and does not count as a rejection"`,
  `it "unavailable_reason names virtio-gpu qemu-only gap and board gap"`,
  `it "detect_virtio_gpu_device false for missing and non-device paths"`.
- **Sabotage**: remove one `self.reject(...)` call → per-op count `it` red.
- **Honesty rule**: no `it` may flip `is_available()`; the live-flip proof exists.

### Unit V2 — virtio-gpu capset/protocol closure
- **Src**: `src/os/drivers/virtio/virtio_gpu_capset.spl` (+`virtio_gpu_types.spl`).
- **Spec**: extend `test/01_unit/os/drivers/virtio/virtio_gpu_capset_spec.spl` (36 its
  landed — inventory-verify overlap first).
- **Functions**: `gpu_le32_read/write` roundtrip incl. high-bit values,
  `gpu_encode_get_capset_info`/`gpu_encode_get_capset` exact byte layout (pinned byte
  vectors), `gpu_decode_capset_info` malformed-length rejection, `gpu_response_type`,
  `gpu_features_have_3d/blob/ctx_init`, `gpu_features_venus_capable`, `gpu_find_venus`
  (present/absent/multiple), `gpu_negotiate_features` (each feature bit arm),
  `gpu_query_capsets`/`gpu_query_capset_info`/`gpu_get_capset` against a fake transport
  that replays canned device responses (pure CPU), `gpu_zero_buffer`, `is_empty`, `is_venus`.
- **its** (new only): `it "le32 write/read roundtrips 0, 1, 0x7fffffff, 0xffffffff"`,
  `it "encode_get_capset_info bytes pinned against virtio spec layout"`,
  `it "decode rejects truncated capset_info without reading past end"`,
  `it "negotiate_features sets exactly the offered∩wanted bits"`,
  `it "find_venus picks venus among multiple capsets and reports absent honestly"`.
- **Sabotage**: byte-swap in `gpu_le32_write` → pinned-byte its red.

### Unit V3 — QEMU virtio-gpu headless smoke (feasible, with container caveat)
- **Files**: create `scripts/check/check-virtio-gpu-capset-qemu.shs` modeled on
  `scripts/os/run_simpleos_q35_smoke.shs` (which already runs `-display none`); add
  `-device virtio-gpu-pci` and a guest probe that runs the capset query path
  (`gpu_query_capsets`) against the real device and prints
  `VIRTIO_GPU_CAPSETS n=<count> venus=<0|1>`; the script greps that line (fail-closed:
  missing line = FAIL, and empty/aborted run = ERROR, never pass — the probe-harness
  fall-through-exit-0 trap).
- **Container caveat (stated honestly)**: needs QEMU in the image and ideally
  `--device /dev/kvm`; without KVM it runs TCG (minutes, still headless — use a 300s
  timeout and mark the wrapper `slow`). If the CI container cannot get `/dev/kvm`, the
  lane still runs, slower. This is a QEMU lane, not a GPU lane — no host GPU needed.
- **Board-runnable note**: per `.claude/rules/board-runnable.md`, boot via OVMF pflash,
  never `-kernel` semantics, never `isa-debug-exit`.
- **Done**: script exits 0 on real capset count ≥1 in QEMU; deliberate sabotage
  (remove `-device virtio-gpu-pci`) exits nonzero with FAIL verdict line.
- **Depends**: V2 (capset code exercised in unit tests first).

### Unit V4 — BLOCKED-ON-HARDWARE (listed, not executable)
- Real-GPU vkcube-equivalent render + readback through `backend_vulkan.spl` sessions.
- Physical-board virtio-gpu / native Vulkan bring-up — blocked on the filed board gap
  referenced in `vulkan_compositor_backend.spl` header and the board-runnable rule
  (aarch64 EFI-stub gap). These units get NO spec files now; they are enumerated here
  so the gap stays explicit. Flipping `is_available()` to true is gated on this unit.

---

## Execution order & parallelism

```
B1  B2  B3            (parallel)
 └────┬───┘
F1 F2 F3 F4 F5 F6 F7 F8 F9   (parallel after B3; F-units touching same spec file serialize)
 └────┬───┘
C1 C2 C3              (each after its module's F-units + B1)
V1 V2                 (parallel, any time after B3)
V3                    (after V2)
V4                    blocked-on-hardware (not scheduled)
```

## Landing discipline (every unit, verbatim)

```bash
cd /home/ormastes/dev/pub/simple
git fetch origin main -q
BASE=$(git rev-parse origin/main)
IDX=/tmp/claude-1000/idx_2dvk_<UNIT_ID>          # fixed per-unit index path
GIT_INDEX_FILE=$IDX git read-tree $BASE
GIT_INDEX_FILE=$IDX git update-index --add <unit file list>
TREE=$(GIT_INDEX_FILE=$IDX git write-tree)
NEWCOMMIT=$(git commit-tree $TREE -p $BASE -F /tmp/claude-1000/msg_<UNIT_ID>.txt)
git diff --stat $BASE $NEWCOMMIT                  # must show ONLY your files
unset GIT_INDEX_FILE
sh scripts/check/check-no-conflict-tree-push.shs $BASE..$NEWCOMMIT
sh scripts/check/check-no-conflict-markers-push.shs $BASE..$NEWCOMMIT
sh scripts/check/check-tree-size-push.shs $BASE..$NEWCOMMIT
GIT_SSH_COMMAND="ssh -o BatchMode=yes -i ~/.ssh/id_ed25519_this_mac" \
  git push git@github.com:ormastes/simple.git $NEWCOMMIT:refs/heads/main
GIT_SSH_COMMAND="ssh -o BatchMode=yes -i ~/.ssh/id_ed25519_this_mac" \
  git ls-remote git@github.com:ormastes/simple.git refs/heads/main   # verify SHA
```
On rejection: re-fetch, confirm your commit's parent is an ancestor, collision-check
YOUR paths only (`git diff --name-only $BASE origin/main | grep -F -f <your list>`),
rebuild the tree on the new base, re-run all 3 guards, re-push. Never force.
Read each guard's verdict line: `PASS`=0, `FAIL`=1, `ERROR — nothing was checked`=2
(2 is not a pass). Push each finished unit immediately — never batch.
