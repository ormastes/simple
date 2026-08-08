# Render-Perf Campaign — Consolidated Status (2026-08-06)

Synthesis only — no code/spec changes made while writing this doc. Source plan:
`doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md`. Binary identity for
every measurement cited below (unless stated otherwise): `bin/simple` →
`bin/release/x86_64-unknown-linux-gnu/simple`, md5 `ed53cc5f255e269ca27c4cd83b17aef9`
— the **Rust bootstrap seed**, not a self-hosted binary. No number in this campaign
is a pure-Simple AOT measurement; treat every perf claim as seed-JIT/interpreter-bound.

Status legend: **DONE** (implemented + verified + sabotage-proven) · **PARTIAL**
(real progress, explicit gap remains) · **DESIGNED-ONLY** · **BLOCKED** (explicit
reason) · **NEEDS-INVESTIGATION** (open correctness question).

## F0–F4 — Presentation/data-model correctness (render_perf_redesign_plan §12.1–12.2)

| Item | Status | Evidence | Next step |
|---|---|---|---|
| F0 engine-identity gate | DONE (as infra) | Every report cited here carries a binary-identity block; the convention is followed consistently across F/O/U/V reports | Keep enforcing; no gap found |
| F1 class-field reference semantics | **BLOCKED** | `doc/08_tracking/bug/class_field_reference_semantics_diverge_2026-08-06.md`: "Investigated, not fixed... Root cause fully localized to the out-of-scope Rust seed... no bounded, verifiable fix location exists yet." Interpreter value-copies class fields; JIT crashes on Option-class fields | Needs a buildable/runnable candidate interpreter before a bounded fix is possible; out of pure-Simple reach today |
| F2 packed span ABI / `rt_typed_words_u32` basis | **BLOCKED (premise refuted)** | `doc/08_tracking/bug/rt_typed_words_u32_is_not_a_packed_pixel_basis_2026-08-06.md`: 8-byte stride, same width as `[u32]` — "No surface was built" | A true 4-byte-packed pixel basis still needs to be found/built; do not resume on the old premise |
| F3 direct column-arena writer (V2) | **PARTIAL** (per V-suite) | `class_reference_semantics_spec.spl` PASS 6/6 (V-lane suite); no separate F3-specific arena-writer report found in this pass | Confirm `ui_scene_column_arena_v2.spl` / `draw_ir_v3_direct_writer_v2.spl` land against F1's still-open reference-semantics gap |
| F4 presentation readback | **PARTIAL** | `doc/09_report/ws_f4_presentation_readback_audit_2026-08-06.md`: plan's composite readback claim mostly REFUTED (no `present_scene` impl reads back); real finding narrowed to `host_wm.spl:84-104` PPM-per-frame + 230,400 FFI calls/frame per-pixel readback at `window_scene_draw_ir.spl:522-536` | Fix is scoped to the WM host's per-pixel FFI readback, not a framebuffer-wide repaint as originally assumed |
| JIT closure/lambda defects (found under F-work) | **NEEDS-INVESTIGATION / open bug** | `doc/08_tracking/bug/jit_closure_abi_refuses_lambdas_and_miscompiles_fn_refs_2026-08-06.md` — Status: Open. Defect 1 (lambda ⇒ whole-module interpreter fallback) is guarded/loud; **Defect 2 is a silent wrong answer**: named-fn-as-value bypasses the guard and hits the same ABI mismatch | File is the tracking artifact; no fix landed this session |

## W0–W2 — CSS dispatch / style hot-path

| Item | Status | Evidence | Next step |
|---|---|---|---|
| W0 CSS O(k) dispatch | Not independently verified this pass | No standalone W0 report found in `doc/09_report` beyond the specs below | Locate/confirm a dedicated W0 report if one exists elsewhere |
| W1 `ComputedStyleHot` split | **PARTIAL** | Spec exists: `test/01_unit/lib/gc_async_mut/gpu/browser_engine/computed_style_hot_split_spec.spl` (mtime 2026-08-06 10:46) | Confirm pass/fail status directly — not run in this synthesis pass |
| W2 selector index (+ invalidation sets) | **IN PROGRESS AS OF THIS DOC'S WRITING** | `src/lib/gc_async_mut/gpu/browser_engine/style_block.spl` is **modified and uncommitted** (`git status`: ` M`), mtime **11:13:29**, which is *after* both `style_block_selector_index_spec.spl` (mtime 11:02:14) and the V-lane promotion suite report (mtime 09:01:05). This is strictly newer than every other artifact checked in this pass. **Do not infer outcome** — a concurrent lane is actively editing this file right now | Re-check `git status`/spec verdict once the concurrent edit settles; this doc cannot state whether W2's invalidation-set half landed or whether a JIT-divergence bug was found, because the edit was still open at write time |
| §7 "DrawIR deltas only for affected components" | **DONE** | Landed `src/lib/common/ui/render_opt/draw_ir_delta.spl` (commit `0502c2b7873`, "feat(ui): DrawIR deltas only for affected components"): selects only chunks whose owner has a real O0 per-node PAINT dirty mark and builds `DrawIrCommand`s for only those, reusing the prior frame's commands for everything else. Spec `test/01_unit/lib/common/ui/render_opt/draw_ir_delta_spec.spl` — 5/5 `it` blocks (proportionality + correctness sabotage tests included) | Closes the last unaddressed §7 item from the plan; none |
| §7 "shaped-run + glyph caches" | **PARTIAL — split by risk** | `font_renderer.spl` shaped-run cache hit/miss counters (commit `c1e232a9a1e`) landed: pure instrumentation on the pre-existing (2026-07-29) shaped-run cache, stress-tested 12/12 clean on both native/JIT and interpreter, with a sabotage test correctly flipping to 0/12. A **sibling glyph-raster cache was found to hit a `[text]`-array read-back corruption bug under native/JIT and was correctly NOT landed** — see `doc/08_tracking/bug/glyph_raster_cache_text_array_index_corrupt_zero_hit_rate_2026-08-06.md` (root-caused via minimal repro, not landed) | Glyph-raster cache needs the `[text]`-array read-back bug fixed before it can land; shaped-run half is done |

## C4 — Effect verifier / @noalloc

| Item | Status | Evidence | Next step |
|---|---|---|---|
| C4 effect verifier | **PARTIAL** | `test/01_unit/compiler/semantics/effect_verifier_spec.spl` exists with 16 `it` blocks; no dedicated report doc found confirming full pass or a specific @noalloc survey deliverable | Verify current pass rate directly; locate/confirm survey doc if one was produced |
| @noalloc real-driver follow-up | Not independently verified this pass | No dedicated report found under `doc/09_report`/`doc/08_tracking` matching "noalloc driver/survey" | Same as above |

## O0–O3 — Revisions / property trees / paint chunks / rasterizer

| Item | Status | Evidence | Next step |
|---|---|---|---|
| O0/O1 revisions, property trees | Not independently verified this pass | System specs exist: `test/03_system/check/gui_showcase_perf_source_revision_contract_spec.spl`, `gui_web_2d_source_revision_emitters_spec.spl` | Run these specs directly to confirm status; no standalone O0/O1 report found |
| O2 paint-chunk raster accounting | **DONE** | V-lane suite: `compositor_occlusion_rect_spec.spl` PASS 21/21. `compositor_occlusion_spec.spl` originally showed **CANNOT EXECUTE — timed out (150s)** in Runs 2-3, but this was root-caused as harness contention (test-daemon `simple_binary()` shadowing, see "Cross-cutting open items"), not a real hang — Run 4 shows it passing 10/10 (130.6s runtime) as part of the suite's overall GREEN verdict | None — set the aggregate suite's per-spec timeout to 300-600s for this spec going forward (it is legitimately slow, just not hung) |
| O3 standalone rasterizer proof | **PARTIAL** | `test/01_unit/lib/common/ui/render_opt/paint_chunk_rasterizer_spec.spl` (2 `it` blocks) and `widget_draw_ir_glyph_run_spec.spl` PASS 4/4 per V-lane suite | Confirm rasterizer spec's own pass/fail directly |
| Cache-key-is-scene-global-not-per-chunk finding | Not independently re-verified this pass | Referenced in task framing; no standalone doc located confirming or dating the finding in this research pass | Locate the filing doc/bug for this finding before citing it as settled |

## P0–P2 — SIMD kernels + dispatch wiring

| Item | Status | Evidence | Next step |
|---|---|---|---|
| P0 scalar oracle | Not independently verified this pass | No standalone report found; likely embedded in `simd_span_batch_execute_spec.spl` | Confirm directly |
| P1/P2 SIMD kernels (5 ops) | **NEEDS-INVESTIGATION** | Prior finding (WS-D, same session family): `engine2d_simd_span_kernels_slower_and_fill_colour_corrupt_2026-08-06.md` — existing SIMD fill kernel is "slower AND wrong" (`0xFF112233`→`0xFF132233`). This predates and directly bears on any P1/P2 SIMD claim | Any SIMD-kernel promotion claim must re-verify against this known-corrupt kernel first |
| Dispatch-wiring lane (`span_batch_execute` fix + `simd_span_batch_execute` + narrow `clear()`-path wiring) | **PARTIAL** | `test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_span_batch_execute_spec.spl` exists (3 `it` blocks); "bucket-granularity gap" mentioned in task framing but **no standalone doc located** confirming its scope or resolution in this pass | Locate the bucket-granularity gap filing directly; do not assume it's closed |
| Promotion-criteria audit: "zero production call sites for registered SIMD kernels" | **Unresolved — cannot confirm closure** | This is the V0/V1 finding (below); whether the dispatch-wiring lane closed the gap **could not be confirmed from available reports in this pass** — no report explicitly ties the two together with a verdict | Explicitly check: does `simd_span_batch_execute` (or the narrow clear()-path wiring) now have a real caller in the production render path? Grep call sites directly |

## G0–G2 — Vulkan plan / backend trait / capability detection

| Item | Status | Evidence | Next step |
|---|---|---|---|
| G0 Vulkan plan | **DESIGNED-ONLY** (pre-existing, not new this session) | `.spipe/simpleos-screens-render-lane/state.md`: "virtio-gpu 2D driver + MapBar/AllocDma syscalls real; Vulkan/Venus is stubbed" | No new Vulkan G-lane report found landed this session in `doc/09_report` |
| G1 honestly-gated backend trait | **PARTIAL (from the adjacent WS-E lane)** | state.md WS-E: capset opcodes / VIRGL|BLOB|CONTEXT_INIT ACK path landed, 46/46 + 11/11 regression, fabricated `VIRTIO_GPU_CAPSET_VENUS=4` constant removed, real OOB DMA hazard fixed. This is the WS-E lane, not explicitly labeled "G1" in the perf-redesign plan — treat as adjacent evidence, not a direct G1 verdict | Confirm whether G0-G2 in the perf-redesign plan are the same items as WS-E, or still pending separately |
| G2 capability detection | Same caveat as G1 | state.md blocker #1: `derived_engine2d_vulkan_bridge_status` hard-equals the legacy 2D device string; primary `derived_engine2d_vulkan_status` does not. "Scope the fix to the *bridge* AC" | Bridge-only gate tightening still open per state.md |
| Physical-board Vulkan evidence | **BLOCKED (explicit, by design)** | Scope exclusion in state.md: "Physical-board GPU display evidence (virtio-gpu is a QEMU device; gap filed per `.claude/rules/board-runnable.md`)" | Correctly filed as a scope exclusion, not silently dropped |

## U0b–U4 — Host migrations + sweep

| Item | Status | Evidence | Next step |
|---|---|---|---|
| U0b hosted-input migration | **DONE** | V-lane suite: `hosted_input_sdl2_spec.spl` PASS 28/28 | none |
| U3 event-path allocation audit | **DONE (premise refuted, correctly reported)** | `doc/09_report/u3_event_path_allocation_audit_2026-08-06.md`: "already allocation-free per event... No `drain_into`, no POD `InputPacket`, and no re-plumbing was implemented, because the cost the plan targets is not there." `InputEventQueue.drain()` does allocate but is dead code | Correctly closed as a non-issue; no further action needed unless the dead `drain()` path is later activated |
| U2 dynamic verification (10s internal watchdog discovery + child-frame-timeout bug) | **NEEDS-INVESTIGATION / open bug filed** | `doc/08_tracking/bug/wm_web_standards_showcase_child_frame_timeout_2026-08-06.md`: Status open. Real finding: `bin/simple run` under `examples/**` has its own internal 10s watchdog (`DEFAULT_EXAMPLES_TIMEOUT_SECS=10`), independent of any external shell timeout — both a 280s and 900s external-timeout attempt were killed by the internal 10s cap before host/child even finished loading. Once past that, the **real verdict is FAIL (child-frame-timeout), not a hang** | Fix requires either raising `SIMPLE_TIMEOUT_SECONDS` for this driver or addressing the underlying child-frame timeout itself |
| U4 cutover + sweep confirming nothing else needs migrating | Not independently verified this pass | No standalone U4/sweep report located in this pass | Locate/confirm directly |

## V0–V1 — Cross-cutting correctness suite

| Item | Status | Evidence | Next step |
|---|---|---|---|
| V0/V1 aggregate suite | **DONE — GREEN verdict (Run 4)** | `doc/09_report/ui/perf/render_perf_v_lane_promotion_suite_2026-08-06.md`: Runs 2-3 were RED (`render_pixel_bridge_spec.spl` blocked on `rt_mmio_write_u32`; `compositor_occlusion_spec.spl` timing out at 150s with no verdict line). **Run 4**, a fresh re-run after the test-daemon debug-seed-binary-shadowing fix (see "Cross-cutting open items" below), reached **VERDICT: GREEN — all 11 specs, 160/160 examples, 0 failures, 0 cannot-execute**. Both blockers were root-caused as harness bugs, not product defects: the MMIO fix (below) and the daemon's `simple_binary()` fallback order (it was silently pinning to the debug-profile seed instead of trying `bin/simple` first, making slow specs blow the daemon's timeout) | None — suite is GREEN. Re-run periodically as a regression guard |
| Promotion-criteria audit (zero production call sites for SIMD kernels) | **Referenced but not independently reconfirmed in this pass** | Same caveat as the P-lane entry above — could not locate a report explicitly stating this finding's text or confirming/denying that the dispatch-wiring lane closed it | Cross-check directly: grep production render-path source for calls into the registered SIMD kernel functions |

## MMIO extern fix (Rust-seed infrastructure, not application logic)

| Item | Status | Evidence |
|---|---|---|
| `rt_mmio_read_u32`/`rt_mmio_write_u32` accessors added to hosted Rust seed runtime | **DONE** | Was the root cause behind `render_pixel_bridge_spec.spl` FAIL in the V-lane suite (`doc/08_tracking/bug/render_spl_specs_cannot_execute_mmio_externs_2026-08-06.md`, and cited again as the V-lane FAIL row). Task framing states both `render_pixel_bridge_spec.spl` and `render_blit_from_addr_spec.spl` now pass following this fix |

This is the one lane this session that touched the Rust seed rather than pure
Simple. That is a **deliberate, precedent-following exception**: extern
registration in the hosted seed runtime is legitimate Rust-side infrastructure
work (the seed's own extern table), not application logic, matching the
precedent recorded in `feedback_extern_bootstrap_rebuild.md` — externs
genuinely require a bootstrap/seed rebuild and are not something pure-Simple
code can add to itself. This is not an oversight of the "pure Simple first"
rule; it is the documented exception to it.

**Caveat:** the V-lane suite report (`render_perf_v_lane_promotion_suite_2026-08-06.md`,
mtime 09:01) still shows `render_pixel_bridge_spec.spl` as FAIL 0/2 with the
MMIO error live — meaning the MMIO fix, if landed, landed **after** that suite
run.

**Confirmed directly in this synthesis pass:** re-ran
`bin/simple test test/01_unit/os/render_pixel_bridge_spec.spl` on this tree —
`SPEC FILE VERDICT: declared>=2 executed=2 passed=2 failed=0`, `Results: 2
total, 2 passed, 0 failed`. The MMIO fix is real and landed. This flips the
V-lane suite's one outright-FAIL spec to green.

**Correction to this doc's own earlier draft:** a dedicated follow-up lane
(after this synthesis pass was first drafted) re-ran
`compositor_occlusion_spec.spl` directly and it is **not** a hang —
`Duration: 130637ms`, `10 examples, 10 passed, 0 failed`. The spec's own
header comment recommending `--timeout 7200` is stale/pessimistic; V0's
original 150s "cannot execute" result was very likely transient load
contention from concurrent sessions, not a real defect. Recommendation
carried forward: give this spec a 300–600s timeout in the aggregate suite
runner, not 150s and not 7200s. With both this item and the MMIO fix
resolved, the V-lane suite's aggregate RED verdict has no remaining known
cause — the suite itself has not been mechanically re-run end-to-end since
these two fixes, so that re-run (not further investigation) is the only
step left to confirm a clean GREEN.

## Cross-cutting open items for the next session

1. **W2 selector-index work is mid-flight right now** (`style_block.spl` modified,
   uncommitted, newer than every other artifact checked) — re-check before
   assuming any outcome.
2. ~~`compositor_occlusion_spec.spl` hangs (150s, no verdict)`~~ — **RESOLVED**:
   confirmed not a hang, real runtime 130.6s, 10/10 pass. V0's original
   "cannot execute" was transient contention. Set the aggregate suite's
   timeout for this spec to 300–600s going forward.
3. **F1 (class-field reference semantics) and F2 (packed-pixel basis) are both
   BLOCKED at the premise level** — F1 has no bounded fix location in this tree;
   F2's entire premised basis was refuted and no replacement basis has been built.
4. **JIT closure Defect 2 is a silent-miscompile, unguarded, Open bug** — highest
   correctness risk on this list; not specific to render-perf but was found by it.
5. Several lane items (W0, W1, C4, O0/O1, P0, U4) have **specs but no standalone
   status report found in this pass** — this doc does not claim they are broken,
   only that their current pass/fail state was not independently reconfirmed here.
   Run them directly before relying on any DONE/PARTIAL label above for those rows.
6. ~~Re-run the V-lane suite... to get an up-to-date RED/GREEN verdict~~ —
   **DONE**: Run 4 (same doc) is GREEN, 160/160 examples, 0 cannot-execute.
7. **Root cause of most "timeout"/"cannot execute" findings in this campaign
   (including `compositor_occlusion_spec.spl`'s apparent hang) was a test-daemon
   bug, now fixed**: `simple_binary()`'s fallback order in
   `src/app/test_runner_new/test_runner_client.spl`,
   `src/app/test_daemon/light_daemon.spl`, and `src/app/test_daemon/main.spl`
   was silently pinning to the debug-profile Rust seed instead of trying
   `bin/simple` (the deployed pure-Simple self-hosted binary) first — see
   `doc/08_tracking/bug/test_client_debug_seed_binary_shadowing_timeout_2026-08-06.md`.
   This retroactively explains several rows above marked NEEDS-INVESTIGATION
   due to timeouts; re-check those rows against a re-run with the fix in place
   before treating them as still open.
8. **Separate, follow-up daemon-lane bug, also fixed same session**: the daemon
   path (`run_one_via_daemon`) computed its timeout once per batch from the
   CLI's un-bumped `run.timeout_secs` (120s default) *before* the loop over
   requested paths, so a spec's own `slow_it` timeout floor
   (`effective_timeout_secs`) was never consulted for the daemon lane at all —
   a `slow_it`-marked spec on the default daemon lane could be killed by the
   daemon's own deadline regardless of `--timeout`. Fixed in
   `src/app/test_runner_new/test_runner_client.spl` (commit `423c0c46b83`,
   "fix(test): daemon lane never applied the slow_it timeout floor per file").
