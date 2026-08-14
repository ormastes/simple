# Render Performance Redesign Plan (2026-08-06)

Diagnosis (claim-verified): `doc/01_research/ui/perf/render_perf_diagnosis_2026-08-06.md`.
Relationship to existing plans:

- `doc/03_plan/os/simpleos/screens_showcase_2d_opt_plan.md` (workstreams A–E)
  remains the SimpleOS screens umbrella. This plan is the deeper perf/compiler
  redesign it feeds into. Overlaps and supersessions are listed in §12.
- The unified packed-scene campaign (L0–L9, landed) is the physical scene
  basis. This plan is **additive V2 repair**, not a new scene architecture.
  No GuiIR/WebIR (standing rejected decision).

## 0-B. 8K80 HARDENING ACCEPTANCE (2026-08-14) — current execution contract

This section supersedes the older resume ordering in §0-A for the physical
8K80 evidence campaign.  Mechanism completion and isolated primitive timing
remain useful, but neither is an end-to-end 8K80 claim.

### Acceptance items

- [ ] **A1 — physical adapter attribution (PARTIAL):** current retained rows
  name the NVIDIA RTX A6000 and record device type plus vendor/device/driver/API
  identity, but the retained report set does not preserve the wrapper's stable
  device-identity hash.  Promote only after that hash is present in the durable
  report, not merely transient stdout.
- [x] **A2 — exact retained primitive oracle:** the timed interval has zero
  readback, while an untimed device-origin oracle records mismatches and a
  nonzero checksum.  The 1% clear row and mixed retained batch satisfy this
  only at primitive/batch scope.
- [x] **A3 — bounded 8K workload:** viewport is exactly 7680x4320, warmup and
  sample counts are explicit, p50/p95 use the 12.5 ms budget, and changed-pixel
  scope is recorded.  Full repaint remains a measured failure; retained damage
  is mandatory.
- [ ] **A4 — production-native DrawIR frame:** a non-seed pure-Simple artifact
  must execute the retained DrawIR workload with backend identity, considered
  and culled command counts, p50/p95, max RSS, checksum, readback source/count,
  and fail-closed fallback/completion fields.
- [ ] **A5 — retained semantic producer frame:** Web, GUI, or WM must publish
  the changed revision through canonical Draw IR and Engine2D; a C ABI probe or
  direct compute benchmark cannot satisfy this item.
- [ ] **A6 — physical presentation:** the same physical device must present a
  7680x4320 changed frame and a retained replay with zero timed host readback,
  native present mode, p50/p95, memory receipts, and device-origin or captured
  scanout parity.  Headless compute and Xvfb are explicitly inadmissible.
- [ ] **A7 — 80 Hz promotion:** A4–A6 each pass p95 <= 12,500,000 ns with no
  CPU/interpreter/stub fallback and no unknown completion.  Claims are scoped
  to the measured damage class and named hardware.
- [ ] **A8 — physical 80 Hz display evidence:** EDID/connector/mode evidence
  must identify an attached 7680x4320@80 display path.  If the host cannot
  expose that mode, the campaign ends WARN rather than fabricating scanout.

### Current blockers and next action

1. **B1 — self-hosted artifact unavailable (blocks A4/A5).** The deployed
   non-seed launcher exits `missing command`; the bounded GUI native renderer
   build exceeds 30 seconds; `bin/simple_native` terminates before provenance.
   Fix or deploy the pure-Simple execution/native-build owner, then run the
   canonical sparse DrawIR receipt once.
2. **B2 — retained Vulkan JIT proof invalid (blocks promotion of an otherwise
   1.54 ms p95 row).** The composed runner recorded RSS as zero and checksum as
   zero, then SIGSEGVed when exact retained samples were enabled.  Fix the
   host-buffer sampling/lifetime boundary; timing alone is not admissible.
3. **B3 — no physical scanout path (blocks A6/A8).** The RTX A6000 lacks
   `VK_EXT_headless_surface`; Xvfb presentation measures 70–79 ms and is not a
   direct-display proxy.  Admission requires a visible/direct-display WSI
   surface and an attached 8K80 mode.  Preserve this as an environmental WARN
   if no connector exposes the mode.

2026-08-14 fresh-lane result: the hardened physical admission returned
`blocked:missing-physical-display`; sysfs exposes only one connected HDMI path,
with modes no larger than 1920x1080.  The one permitted Xvfb regression passed
its device-present proxy contract on the RTX A6000 but measured 193.681044 ms
p95, so it remains inadmissible for A6–A8.  A physical 8K80 result is therefore
**WARN / hardware-blocked**, not PASS.

The lane must address B1 and B2 in software before treating B3 as the terminal
environmental gate.  Do not start unrelated O/P/G expansion while A4–A6 are
open.  Canonical evidence sources are the 2026-08-12 reports under
`doc/09_report/` and their linked open bugs under `doc/08_tracking/bug/`.

### Implementation handoff — blocked rows remain active

This is an implementation handoff, not feature completion.  Each row keeps its
acceptance ID, missing prerequisite, exact resume command, retained artifact,
owner, and independent final reviewer.  A future run may update a row only from
fresh evidence produced by that command on the named capability.

| Row | Missing prerequisite and exact resume command | Retained artifacts | Owner / final reviewer |
|---|---|---|---|
| **A1** | Preserve the stable device-identity hash emitted by the physical adapter probe in the durable report, then have the physical wrapper validate it as nonzero alongside the textual identity. The unavailable-hardware execution contract is owned by TODO685. | `build/check/engine2d-vulkan-window-8k/run.*/receipt.env`; `doc/09_report/engine2d_vulkan_clear_8k_evidence_2026-08-12.md` | Vulkan evidence owner / independent highest-capability Codex |
| **A4** | Produce an admitted non-seed pure-Simple executable: `mkdir -p build/render_perf && SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1 timeout 300 bin/simple native-build --source src/lib --source test/05_perf/graphics_2d --entry-closure --entry test/05_perf/graphics_2d/draw_ir_damage_8k_bench.spl --runtime-bundle core-c-bootstrap --backend cranelift --opt-level=aggressive --output build/render_perf/draw_ir_damage_8k_bench`; then execute it directly once: `SIMPLE_NO_STUB_FALLBACK=1 timeout 300 /usr/bin/time -v -o build/render_perf/draw_ir_damage_8k_bench.time build/render_perf/draw_ir_damage_8k_bench >build/render_perf/draw_ir_damage_8k_bench.stdout 2>build/render_perf/draw_ir_damage_8k_bench.stderr`. | `build/render_perf/draw_ir_damage_8k_bench*`; `doc/08_tracking/bug/draw_ir_8k_native_evidence_blocked_2026-08-12.md`; refresh `doc/09_report/drawir_sparse_dynamic_8k_attempt_2026-08-12.md` | pure-Simple native-build owner / independent highest-capability Codex |
| **A5** | After an admitted non-seed compiler exists, run `BENCH_TIMEOUT_SECS=300 BUILD_DIR=build/render_perf/gui_8k80 REPORT_PATH=build/render_perf/gui_8k80/gui_8k80_semantic_producer.md bash tools/gui_perf_bench/run_all_benchmarks.shs --width 7680 --height 4320 --frames 60 --dpi 300`; require the `backend_measurement_software_export.native` route to publish the canonical semantic producer frame through Draw IR and Engine2D, with no interpreter or seed fallback. | `build/render_perf/gui_8k80/gui_8k80_semantic_producer.md` and sibling receipts; publish the accepted result to `doc/09_report/ui/perf/gui_8k80_semantic_producer_<date>.md` and refresh `doc/09_report/web_renderer_retained_damage_plan_evidence_2026-08-12.md` | UI render producer owner / independent highest-capability Codex |
| **A6** | Physical hardware execution is tracked by canonical Todo DB item TODO684; this plan retains only the acceptance dependency. | TODO684 evidence | physical Vulkan/display operator / independent highest-capability Codex |
| **A7** | After A4–A6 pass, implement the missing parent-authoritative `scripts/check/check-render-perf-8k80-completion.shs` aggregator tracked by `doc/08_tracking/bug/render_perf_8k80_completion_aggregator_missing_2026-08-14.md`, then run `BUILD_DIR=build/render_perf/8k80_completion sh scripts/check/check-render-perf-8k80-completion.shs --drawir build/render_perf/draw_ir_damage_8k_bench.stdout --producer build/render_perf/gui_8k80/gui_8k80_semantic_producer.md --physical build/check/engine2d-vulkan-window-8k/run.*/receipt.env --report doc/09_report/ui/perf/render_perf_8k80_completion_<date>.md`. It must require p95 `<=12500000 ns`, complete RSS/checksum/readback receipts, no CPU/interpreter/stub fallback, and known completion. | `doc/09_report/ui/perf/render_perf_8k80_completion_<date>.md` plus the exact A4–A6 receipts | root integration owner / independent highest-capability Codex |
| **A8** | Physical connector, EDID, and scanout evidence is tracked by canonical Todo DB item TODO685; this plan retains only the acceptance dependency. | TODO685 evidence | physical display operator / independent highest-capability Codex |

### Cooperative review record

- SPipe state: `.spipe/rendering_physical_8k80_plan_completion/state.md`.
- Lower-model ledger sidecar: audited A1–A8 and found the former A1 durable-
  hash overclaim; the correction above is load-bearing.
- Lower-model guide/wiki sidecar: refreshed the feature and layer expert pages
  named below with the canonical wrapper and blocked-row resume contract.
- Merge owner: root Codex lane in the isolated `restart12-render_8k` worktree.
- Generated-manual review: N/A — this handoff changes no executable SSpec or
  generated manual; `doc/06_spec` layout remains a verification gate.
- Final acceptance owner: separate highest-capability Codex reviewer must
  accept ledger truthfulness, guide/wiki freshness, exclusions, retained
  blockers, and all done marks before this handoff can land.

## 0-A. STATUS OVERLAY (added 2026-08-09, revised 2026-08-09) — historical baseline

This overlay was added because the plan below carried almost no status markers
while a large part of its surface had already been built, **some of it out of
the plan's own stated order**. The prose below §0-A is the ORIGINAL plan and is
deliberately unedited; where it disagrees with this overlay, the overlay is
newer. Every SHA here was verified present on `main` (fetched tip, not the local
`origin/main` ref, which lags) on 2026-08-09.

### Standing caveat — no perf number is admissible yet

`bin/simple` is still the **Rust seed**. Per §11, no perf claim produced by the
seed or the tree-walk interpreter is admissible. Everything landed so far gates
the **mechanism** (measured-bits, counted refusals, ABI width, engine identity),
**not any performance number**. Do not read a green gate as a met milestone.
Nothing landed on 2026-08-09 moves this: the day's evidence is seed- or
stage2-attributed throughout, and **nothing proves the self-hosted or native-AOT
lane**.

### Ordering inversions — the reason this overlay exists

1. **F3 and the F2 Simple-side primitive landed BEFORE F1, together, on
   2026-08-06** — commit `deea048b59f` added `packed_span.spl`,
   `ui_scene_column_arena_v2.spl`, `draw_ir_v3_direct_writer_v2.spl` and two
   specs in **one commit**, two days before any F0/F1 work existed. §2's stated
   critical path is `F1→F2→F3`; the tree was built `F3+F2ʹ → F2ʺ → F0 → F1`.
   Consequence: **UiSceneColumnArenaV2's zero-copy property is engine-dependent
   and unproven until F1 lands.** It rests on a class/reference contract the
   compiler does not yet have.
2. **C1 and C4 are fixture-fed, not source-fed, in part.** C1's obligations 1–4
   are proven against real layout; **5–8 run at neutral defaults** because
   `TypeLayout`/HIR carry no per-field facts for them — a neutral default is not
   a proof. C4's verifier is complete but still fed by fixtures; source wiring
   is in flight. Treat both as PARTIAL, never as green.
3. **C5 emits `ZFP_UNMEASURED` for three of four axes.** Only the hop axis is
   measured. The other three are BLOCKED-by-design rather than assumed zero —
   which is correct, but means §0's five-zero milestone is one-fifth measured.

Treat every marker in the table below as claim-verified only for the SHA cited.
An earlier revision of this table said "O0–O4 NOT STARTED" while O0/O1/O2 were
already partially built; markers here have been re-derived from git history, not
carried forward.

### Lane status

| Lane | Status | Evidence |
|---|---|---|
| **F0** receipts + engine-identity gates (not a numbered §; serves §0/§11) | **LANDED `64dbe3b01c8`** | `src/lib/common/perf/render_perf_receipt_v2.spl` (per-counter `measured` bit, `perf_milestone_gate`, `RenderPerfGateLedger`, never-merged verdict families `refuse:*` / `blocked:unmeasured:<n>` / `fail:nonzero:<n>=<v>`), `scripts/check/check-render-perf-milestone-gate.shs` (fatal selftest). Closed a real fabricated-zero hole: counters initialised to 0 with no record of whether anyone wrote them read as five perfect zeros. Gates mechanism only — see caveat above. |
| **F1** class/reference semantics | **BLOCKED — unchanged 2026-08-09** | Plan `a4eb22fa77d` → `doc/03_plan/ui/perf/f1_class_identity_kind_propagation_plan_2026-08-09.md` (**not** under `doc/03_plan/compiler/`). Corpus + JIT struct-alias defect `47a162e079a`. The seed has **zero** `ClassKind` / `StructKind` / `TypeKind::Class`; `is_value_type` is set at the parser then **hardcoded at 13 literal sites** across `context_pack.rs`, `hir/lower/module_lowering/module_pass.rs:548` (`false`), `interpreter/node_exec.rs:438` (`true`), `interpreter_call/block_execution.rs`, `interpreter_eval.rs`. Engines fail in OPPOSITE directions (interpreter copies classes; JIT aliases structs), so no single-backend patch works. Staged S1–S5; **S2 (a driver reaching the pure-Simple engine) must precede S1.** Still the front of the queue. |
| **F2** packed span ABI | **PARTIAL (both halves present)** | Simple primitive landed `deea048b59f` (08-06, with F3); counted refusal gate `cf36e6d6200`; C half `dc201577385` → `src/runtime/runtime_packed_span.{c,h}`, magic-first struct, `sizeof == 40`, alignment 8. One-check-per-batch measured: 1 resolve call admitting 16384 elements. `packed_span_backend_name()` is a **live per-engine probe, not hardcoded** (reports `scalar-oracle` where the engine cannot deliver). **Criterion 7 remains PARTIAL — blocked by a stdlib MIR `HirTypeKind::Infer` gap.** |
| **F3** UiSceneColumnArenaV2 | **PARTIAL — built on absent foundations** | `deea048b59f` (08-06): `src/lib/nogc_sync_mut/ui/ui_scene_column_arena_v2.spl`, `draw_ir_v3_direct_writer_v2.spl` + specs. Landed **before** F1 and alongside F2ʹ. Zero-copy unproven until F1. |
| **C0** layer declarations | **LANDED** | Soft keyword, `@layer(NAME)`, DAG errors implemented. |
| **C1** layer-equivalent types | **PARTIAL** | `c0b284e6a5f` — `@layer_eq`/`@layer_field` parse and reach the checker on **real source** (`10.frontend/layer_eq_registry.spl`, `35.semantics/layer_eq_validation.spl`, parser + HIR pipeline wiring). Obligations 1–4 proven against real layout; **5–8 at neutral defaults** (missing `TypeLayout`/HIR per-field facts). |
| **C2** typed forwarding | **IN FLIGHT** | — |
| **C3** logical AOP join points | **PARTIAL — static weave landed for ONE join-point kind (was "NOT STARTED")** | `5f13a5f3dc5`: `src/compiler/35.semantics/aspect_weave.spl` + `driver_hir_pipeline_lowering.spl` wiring + `test/01_unit/compiler/semantics/aspect_weave_spec.spl`. Weaves the **`forward`** join-point kind only — the other six kinds stay unwoven because `join_point_kind_is_measurable` cannot prove them. The commit also fixed a real write-back bug that silently lost **every** weave. `39a216bf843` corrected two spec oracles that asserted a post-weave statement count against un-woven bodies: `HirBlock` stores a single tail expression in `.value`, not `.stmts`, so the un-woven baseline is 0, not 1 — the spec is now 5/5. Seed/interpreter evidence only. |
| **C4** effect verifier | **PARTIAL** | Verifier complete but **fixture-fed**; source wiring in flight. |
| **C5** `@zero_forward_path` gates | **PARTIAL — hop axis LANDED `3fc73b79b11`** | `src/compiler/35.semantics/zero_forward_path_gate.spl`. Hop axis bites; the other three axes emit `ZFP_UNMEASURED` → BLOCKED rather than assumed zeros. |
| **U0–U3** WM/GUI/Web/events adoption | **PARTIAL — hit-test divergence CLOSED `3166165f0e3`** | Events `945f7bde756`: `src/os/drivers/input/input_batch.spl` — `drain_into`, coalescing policy that **never merges key/text/focus/close**, allocation gate asserting F0 returns `blocked:unmeasured:allocations`. Hit-test boundary agreement `1b8c772792f` had proven the two stacks diverge on `z_index`, `enabled=false` and `pointer_policy=None` because `DrawIrV3Command` carried no such columns — **a disabled overlay ate clicks on the packed path**. `3166165f0e3` adds `z_indices` / `enableds` / `pointer_policies` columns to the DrawIrV3 hit-test table (`DRAW_IR_V3_SCHEMA_ID` 3→4) and threads them through `draw_ir_v3_emit_full`, `draw_ir_v3_group_resolve`, `ui_scene_arena` and all three packed producers (wm/gui/web); `event_route_stack_boundary_agreement_spec.spl` was rewritten accordingly. Still open: SPSC atomics, POD `InputPacket` (`ch: text` is a heap ref), `RouteToken`, allocating flat hit-test path. |
| **O0** revisions/invalidation | **PARTIAL (mechanism only)** | `src/lib/common/ui/render_opt/revisions.spl`: `RenderRevisions` with an explicit 8×8 propagation matrix (no bitmasks, no enums — engine-portable integer indexing), `mark`/`is_dirty`/`dirty_nodes`/`total_dirty`, in-band `mark_count`. The load-bearing TRANSFORM row marks one column. Gate: `test/01_unit/lib/common/ui/render_opt/render_opt_invalidation_spec.spl` describe (a), 8/8. **Mechanism only — no perf number, see the standing caveat.** |
| **O1** property trees / retained chunks | **PARTIAL (mechanism only)** | `src/lib/common/ui/render_opt/property_trees.spl`: `PropertyTrees` (transform/clip/effect/scroll + exact damage rects), `PaintChunks` with the §4-pass-3 cache key, `paint_chunks_sync`. `paint_chunks_property_rev` deliberately EXCLUDES `PT_TRANSFORM` — that exclusion is what makes a transform-only move cost zero chunk rebuilds. Gate: same spec, describe (b), 7/7, incl. live-key controls that fail if the key were inert. |
| **O2** damage / raster skip | **PARTIAL (raster-skip half only)** | `paint_chunks_raster` → `RasterStats{rastered,skipped,bytes_painted}`; quiescent frame rasters 0. Gate: same spec, describe (c), 3/3, plus `paint_chunk_rasterizer_spec.spl` 9/9 and `draw_ir_delta_spec.spl` 6/6. **The occlusion/visibility half (§4 pass 5) and the multi-scale dirty-TILE sets (§4 pass 4: coarse grid / CPU tiles / GPU bins, profile-measured) are NOT in this module** — the only occlusion code is the compositor-level baseline under `src/os/**`. Do not read O2 as complete. |
| **O0/O1/O2 sabotage controls** | **LANDED 2026-08-09** | Same spec, describe (d), 3/3. Each reconstructs the defeating edit inside the spec (TRANSFORM row also marking PAINT; `PT_TRANSFORM` folded into the chunk key; unconditional raster) and asserts the gate's expected value is violated. Meta-sabotage verified: neutralising all three injections turns the file **21/21 → 18/21 with exactly those 3 red**, so none of them is a check that cannot go red. Binary: `bin/release/x86_64-unknown-linux-gnu/simple` — **the Rust SEED** (`--version` prints the bootstrap-seed warning), tree-walk interpreter test path. Correctness evidence only; **not admissible as any perf claim.** |
| **O3–O4**, **P0–P5**, **G0–G4** | **NOT STARTED** | Correctly gated behind §0's milestone. |

### Adjacent defects fixed 2026-08-09 that this plan's surface depends on

These are not lanes, but each was silently corrupting a path the render/perf
work reads or is verified through:

- `724b8d32eeb` — **radial gradients were painting ZERO pixels.** The N-stop
  gradient branch in `draw_ir_adv.spl:683` was gated on flat props nothing ever
  wrote; linear gradients only passed by accident, via a legacy path that
  ignores middle stops and angle. Fix emits the GAP-2 stop props.
- `e5bc26ced33` — interpreter `70.backend/backend/env.spl`: a doubly-indexed
  assignment target plus a descending inclusive range `(n)..=0` that iterates
  **zero** times. This broke any user-to-user function call, i.e. every spec run
  through the interpreter lane.
- `197b61f972f` — `levenshtein_distance` returned **0 for every input**: the DP
  rows are value types, copied out and never written back. Landed with a
  value-type write-back family audit. `48de6604045` closed that audit's `tbl`
  finding as **wrong** — the excerpt was truncated; the write-backs exist at
  `pure_db` :2822 and :2888 and both are sabotage-proven load-bearing.
  Recorded RESOLVED-not-a-defect, with an UPDATE-then-read spec.
- `70a641a4df3` / `d5ddc4371dd` / `b0e0092a5fd` — three native-AOT fences.
  Trailing-default-param (and a repair to the check's own `EXIT` trap, which was
  eating its diagnostics); Option-unwrap receiver lowering, which is the actual
  root cause of the SimpleOS hosted-FAT32 blocker (new fence
  `check-native-option-unwrap-receiver.shs`); and trait-typed **return**
  receivers failing MIR lowering — where trait-typed **optional field**
  receivers are worse still, **silently losing data** (fail-open, not a hard
  error). Also: the `blockdevice-dispatch-codegen-bug` marker at
  `src/os/services/vfs/vfs_boot_init.spl:383` is **STALE** — that defect was
  fixed 2026-07-20; the skip was retained for the Option-unwrap defect.
- `7fb77258f47` — `src/lib/cc/**` is **not** dead code: the audit claim was
  refuted, `src/lib/viz/feature/aggregator_compose.spl:8` is a live consumer of
  `cc/entity/property_tree.spl`. Only `layer.spl` / `layer_tree_host.spl` are
  spec-only. Separately, `doc/04_architecture/ui/drawing_stack.md` lists
  `cc/entity/{layer_base,tile}.spl`, which **do not exist**.

### SimpleOS runnable status (per `.claude/rules/board-runnable.md`)

Rungs: (a) source present, (b) staged into an image, (c) booted under real
firmware, (d) WM actually rendering in-guest.

Bug doc `doc/08_tracking/bug/simpleos_wm_lane_not_board_runnable_2026-08-08.md`
(`f7421f2625e`) is **STALE** — it predates the rung (b)/(c) evidence below.

- **(a) source present — YES.**
- **(b) staged into an image — YES on x86_64** (`e83b3df9596`).
- **(c) booted under real firmware — YES.** x86_64 chain verified end to end:
  OVMF pflash → GRUB `BOOTX64.EFI` multiboot → `[BOOT32]` / `[BOOT64]` → kernel
  `_start` → PMM/VMM → NVMe + FAT32 → framebuffer 3840x2160 argb8888 →
  `engine2d-ready` → `compositor ready`, 3 owned surfaces. **No `-kernel`, no
  `isa-debug-exit`** — real-firmware proxy throughout. Best serial 16,578 bytes.
  aarch64 booted under AAVMF with an 800x600 framebuffer (`bf37f58c41d`); the
  missing framebuffer there was never a kernel bug — QEMU `-M virt` has no
  default display adapter, `ramfb` fixes it. aarch64's own blocker is that
  `memory_init` is still the Layer 1 milestone stub.
- **(d) WM actually rendering — NO. This is an explicit non-claim.**
  `scanout_capture_size=0` on **every** run and no PPM was ever captured, so
  **no compositing evidence exists**. Reaching `compositor ready` is rung (c),
  not rung (d). Do not read the boot chain as rendering.
- **Physical board: ZERO evidence on either arch.** Per the board-runnable rule
  this is a filed gap, not a completion.

**Why the lane was stuck, recorded because it was self-perpetuating:** the gate
hashed a 1,512-file source closure before the build and re-hashed after,
aborting on mismatch **upstream** of disk staging and QEMU — so `qemu.out` /
`serial.log` never existed and `kernel_sha256` was always empty. Every run
therefore rebuilt, and every rebuild lost the race against concurrent-session
churn (17 `src/lib` files changed within one run; a foreign `git am` rewrote
9,386 files mid-build), so no valid admission was ever written and the cache
path could never engage. `92af22801ef` added a bounded build retry; one
successful admission broke the loop, and later runs hit `current-source-cache`
at `attempts=0`. That single fix took the lane from rung (a) to rung (c).

### Measurement traps in this lane — check these before believing a RED

1. **Readiness timeout produced FALSE REDs.**
   `SIMPLEOS_WM_READINESS_TIMEOUT_MS` used to default to 60s, too tight for a
   source-built run on a loaded host. Controlled experiment, identical kernel
   and identical staging: 300s reached full scanout; the 60s run stopped at
   7,068 serial bytes and read as a regression. **The default is now 300000 ms**
   in `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` — verified on
   the current tip, so this trap is closed, but any older transcript showing a
   60s-bounded RED is not evidence of a defect.
2. **Canonical evidence paths are racy, and `serial_log_bytes` is noisy.**
   `build/simpleos_wm_fullscreen_evidence/{serial.log,qemu.out,evidence.env}`
   are overwritten by concurrent sessions mid-flight; run dirs have been
   observed whose contents do not match their timestamps. **Only per-run
   archived copies are trustworthy.** And `serial_log_bytes` is not a progress
   signal: the identical kernel produced 16,578 and 14,207 bytes on consecutive
   runs.

### Resume here — highest-leverage next steps

1. **F1 / S2 — build a driver that reaches the pure-Simple engine.** *Unblocks:*
   everything downstream, because F3's zero-copy and F2's arena guarantees are
   engine-dependent until the class/reference contract is real. S2 must precede
   S1. *Blocked by:* nothing — this is the front of the queue.
2. **SimpleOS rung (d) — get a scanout capture.** `scanout_capture_size` is 0 on
   every run to date. *Unblock condition:* a captured PPM (or equivalent) that
   shows composited output; until one exists there is no rendering claim to
   make, only a boot claim.
3. **C4 source wiring, then C1 obligations 5–8.** *Unblock condition for 5–8:*
   `TypeLayout`/HIR must carry the per-field facts; until then they are neutral
   defaults and must not be reported as proven.
4. **C3 — extend the static weave past `forward`.** Six of seven join-point
   kinds stay unwoven because `join_point_kind_is_measurable` cannot prove them.
5. **F2 criterion 7.** *Unblock condition:* close the stdlib MIR
   `HirTypeKind::Infer` gap.
6. **Do not start O/P/G lanes.** §0's five zeros are one-fifth measured and no
   perf number is admissible while the deployed binary is the seed.

### Working-tree note

Do not verify lane files against the local working copy or the local
`origin/main` ref — both lag, and concurrent sessions (including a live foreign
`git am`) edit the tree mid-session. On 2026-08-09 the WC was missing
`scripts/check/check-render-perf-milestone-gate.shs` while it was present
upstream. Fetch the true tip and read blobs from it.

## 0. Decisive first milestone

Not Vulkan, not AVX-512. A warm frame where:

```
allocations             = 0
scene copy bytes        = 0
full readback bytes     = 0
unchanged raster pixels = 0
physical forward hops   = 0
```

Only then do SIMD/GPU operate on real packed workloads.

## 1. Target architecture

```
WM | GUI | Web  (private semantic state, stable IDs/revisions/deltas)
      ↓ compile-time layer/service views (aliases + forwarding + layer-eq
        types, ERASED before executable MIR)
UiSceneColumnArenaV2  (DrawIR-v3 columns, leases, generations, MutSpan writers)
      ↓ SceneDeltaRef
Common Render Optimizer (revisions, property trees, retained chunks, damage,
                         tiles, culling, conservative occlusion, resources,
                         glyph atlas, batching)
      ↓ PreparedRenderPlan
Placement/Cost Planner (dirty px, op mix, residency, transfer/sync, power)
      ↓                    ↓
CPU plan optimizer     GPU plan optimizer
CpuKernelTable         Common GpuRenderPlan → Vulkan | Metal | D3D12
      └───────── persistent compositor, damage-aware presentation ─────────┘
```

Key distinction: **architectural layers are compile-time boundaries;
optimization layers are plan stages; runtime wrappers are not required for
every architectural layer.** GUI/Web/WM write one packed scene; the optimizer
sees it once; the executor receives one prepared plan.

Layer responsibilities and allocation permissions:

| Layer | Responsibility | Runtime allocation |
|---|---|---|
| L0 semantic | WM windows, widget tree, DOM/CSS/layout | persistent semantic state only |
| L1 layer/service view | dependency check, aliases, forwarding, type projections | none — compiler-only |
| L2 packed scene | DrawIR columns, stable IDs, owners, revisions | session alloc; zero steady-frame alloc |
| L3 common optimization | invalidation, chunks, damage, culling, resources | frame arena / preallocated sidecars |
| L4 placement | CPU/GPU/pass selection + fallback receipts | fixed plan workspace |
| L5 CPU / GPU optimization | spans, kernel selection, tiles / instances, uploads, pass graph | per-thread scratch / persistent rings |
| L6 API backend | Vulkan/Metal/D3D12 encoding | backend-managed persistent pools |
| L7 presentation | swap, composite, partial update, scanout | frame-ring resources only |

## 2. Repair the packed memory path first (critical path F1→F2→F3)

### F1 — class/reference semantics (language contract)

The arena writer's copy workaround exists because a class instance stored as
another class's field is a **value copy under the tree-walk interpreter**
(`draw_ir_v3_native_writer.spl:14-19`, verified) while other engines differ.
Contract to enforce across interpreter, seed JIT, pure-Simple JIT/AOT,
SimpleOS:

- `struct` = value semantics; `class` = identity/reference semantics.
- Assigning a class to a field copies the reference, never the object.
- `clone()` / explicit value-copy required to duplicate.
- Borrowed exclusive access stays exclusive through aliases.
- Tests: nested fields, optionals, arrays of class refs, trait fields,
  function parameters — same corpus, same hashes, every engine.

Until F1 lands, every zero-copy scene abstraction is engine-dependent.

### F2 — packed span ABI

Safe handle, not a raw host pointer:

```
struct BufferSpanRef:
    object_slot: u32
    object_generation: u32
    byte_offset: u32
    byte_length: u32
    element_count: u32
    element_stride: u32
```

Runtime resolves once to `SimplePackedSpanV1 {base, byte_length,
element_count, element_stride, flags}` (C, per the pure-Simple-first / C-not-
Rust hardware policy). Required: no boxing, no temp rows, no gather/scatter,
stale-generation refusal, one bounds/generation check per submitted batch.
Interpreter mode uses the scalar oracle and must not claim SIMD performance.

### F3 — UiSceneColumnArenaV2

New files (frozen DrawIR-v3 schema and v1 port untouched):

- `src/lib/nogc_sync_mut/ui/ui_scene_column_arena_v2.spl`
- `src/lib/nogc_sync_mut/ui/draw_ir_v3_direct_writer_v2.spl`
- `src/lib/common/ui/ui_scene_delta_v2.spl`
- `src/lib/common/ui/ui_scene_ports_v3.spl`

Preallocated front/back columns; direct indexed MutSpan writes; stable
producer partitions + component IDs + generations; dirty byte/ID ranges; no
writer-owned temp arrays; no row-commit copy; no mid-frame compaction; growth
only at frame boundary; typed refusal on partition overflow. Incremental
frames update stable slots and emit:

```
struct SceneDeltaRef:
    scene_generation: u32
    changed_table_mask: u32
    dirty_range_start: u32
    dirty_range_count: u32
    damage_start: u32
    damage_count: u32
```

Producer IDs remain **arena-absolute** (standing lesson: producer-local IDs
pass single-producer tests and break composition).

## 3. Zero-cost layers and typed forwarding (language feature — lanes C0–C5)

### C0 — layer declarations

```
layer draw
layer gui uses draw
layer web uses gui, draw
layer wm uses gui, draw

@layer(gui)
module gui.widgets
```

Rules: acyclic; calls only same-layer or declared-downward; lower layers never
import higher semantic state; events go up via route data, not reverse
imports; layers create no runtime objects.

### C1 — layer-equivalent types (implicit-by-name, explicit-by-tag)

Same-name fields inferred; renames tagged:

```
@layer_eq(draw.DeviceRect)
struct GuiBounds:
    @layer_field(x) left: i32
    @layer_field(y) top: i32
    @layer_field(width) extent_x: i32
    @layer_field(height) extent_y: i32
```

Conversion is a compile-time proof, zero executable ops (same SSA value/
address). Proof covers: size, alignment, field types/offsets, enum
discriminants, ownership/mutability, lifetime, address space, endianness,
unit/coordinate tags, pixel format/color space/alpha, ABI version + dynSMF
fingerprint. NOT layer-equivalent (must stay explicit ops): CssLogicalRect→
DevicePixelRect, straight→premultiplied color, host→device buffer, document→
window point, UTF-8 byte↔scalar index. Type vocabulary: `@unit(css_px)`,
`@space(document)`, `@color(srgb8)`, `@alpha(premultiplied)`.

### C2 — typed forwarding instead of generated wrappers

Keep the surface syntax (`alias GuiPaint = draw`, `fn fill_rect =
draw.fill_rect`) but the parser emits a typed declaration, never a source
body:

```
HirForwardDecl { logical_symbol, receiver_projection, target_symbol,
                 layer_view_map, effect_summary, logical_join_point_id }
```

Compiler sequence: resolve layer DAG → prove layer-eq views → transitive
forwarding graph → assign join-point IDs → weave static aspects → specialize
session service table → collapse chains → erase identity views →
devirtualize single-target calls → inline/SROA → verify noalloc/nocopy/
effects → lower ONE physical call. `WebPainter.submit → GuiPainter.submit →
Draw2DService.submit → CpuRenderExecutor.execute` becomes
`CpuRenderExecutor.execute(plan, target)`.

### C3 — logical AOP join points

Aspects target logical edges (`forward(src,dst)`, `layer_view(a,b)`,
`scene_commit(kind)`, `render_batch(kind)`, `event_route(owner)`,
`fallback(class)`, frame boundary) — a business-logic-free forwarder need not
exist physically for advice to observe it. Three modes: static weave (zero
disabled overhead), startup dynload (immutable AspectPlan before session,
tables specialized once), live reload (plan swap at frame boundary,
epoch/RCU retirement). Never per-pixel/glyph/span/tile join points; hot-path
join points only at frame/commit/plan/batch/submit/event-batch/fallback.
Aspect state in a sidecar keyed by slot+generation; advice declares
`@readonly @noalloc @bounded_time`.

### C4 — effect verifier

`@noalloc`, `@copy_budget(0)`, `@bounded_loop` verified on **post-weave,
post-collapse MIR**: rejects allocator calls, container growth, hidden
boxing, prohibited copies.

### C5 — mechanical gates (`@zero_forward_path`)

Compiler reports per hot entrypoint: `logical_forward_edges=N,
physical_forward_calls=0, layer_view_copy_bytes=0, temporary_allocations=0,
dynamic_dispatches<=1/batch`. Compilation FAILS when a claimed identity view
changes size/alignment/ownership/address-space, needs unit/color conversion,
allocates, copies, or calls a user conversion.

## 4. Common optimizer (lanes O0–O4)

Backend-ignorant `prepare(scene, delta, viewport, capabilities, scratch) ->
PreparedRenderPlanRef`. Ordered passes:

1. **Revisions/invalidation** — separate `semantic/style/layout/paint/
   transform/clip/resource/event` revisions; mutations mark minimal sets.
2. **Property trees** — transform/clip/effect/scroll/surface; window move =
   one transform-node update.
3. **Retained paint chunks** — grouped by owner/transform/clip/effect/
   surface/resources/order; cache key = component_generation +
   paint/property/theme/scale/viewport/capability generations.
4. **Damage** — exact rects for small changes AND dirty tile sets; separate
   scales (coarse grid ~128–256 px, CPU tiles ~32–64 px, GPU bins ~128–256
   px), profile-measured, not hard-coded.
5. **Visibility + conservative occlusion** — cull hidden/zero-area/off-
   viewport/covered-by-provably-opaque; any uncertain alpha/filter/blend/
   rounding/transform disables that occlusion decision; exact paint order
   preserved.
6. **Resource interning/atlases** — content hash + semantic metadata for
   images, gradients, paths, shaped runs, glyph masks, clip masks, pipelines.
7. **Batching/fusion** — only when target, order, blend, clip/effect, format,
   resources, opacity all match; never reorder overlapping translucency.
8. **Pass graph** — backend-neutral `RenderPassNode` DAG + transient
   lifetimes; GPU maps to passes, CPU executes same graph on tiles.
9. **Placement** — per pass/batch on dirty px, op type, residency, transfer/
   sync cost, queue load, latency, power, correctness evidence. Never GPU
   just because one exists; never widest SIMD just because the bit is set.

**Optimization registry**: each optimization = descriptor {stage,
preconditions, capabilities, exactness class, cost model, verifier,
fallback}. Promoted only after: preconditions proven, scalar parity, shadow
execution divergence-free, wins its bucket, p95/memory inside gate, fallback
receipt-backed. (The current SIMD regression — diagnosis claim 1/5 — is the
proof that capability presence is not a promotion criterion.)

## 5. CPU scalar + SIMD (lanes P0–P5)

- **One kernel contract, many providers** (`CpuIsaProvider`: probe,
  register_kernels, self_test vs scalar oracle, calibrate). Registry key =
  operation × pixel format × alpha × alignment × contiguity × size bucket ×
  mask × filter. Session builds one `CpuKernelTable` once.
- Size buckets: 0–15 scalar; 16–63 scalar/narrow; 64–255 SIMD; 256+ SIMD
  possibly threaded; large overwrite = measured streaming-store variant.
- Providers: x86 (scalar/SSE2/SSSE3-SSE4.1/AVX2/AVX-512BW-VL — separate
  variants, fixes today's `Avx512→"avx2"` aliasing), AArch64 (Neon, SVE/SVE2
  VLA), Arm32 (optional Neon), M-profile (optional MVE), RISC-V (RVV 1.0
  strip-mined, Zve profiles); future providers register, never extend a core
  enum.
- Kernel set v1: fill_const, copy_span/rect, scroll_rect, src_over_const/
  image, mask_src_over, glyph_mask_blend, nearest/bilinear_blit, linear/
  radial_gradient, format_convert, (un)premultiply, blur_h/v,
  coverage_combine. Kernels receive packed spans or `SimpleSpanOpV1` batches
  — **one batch FFI call**, never boxed arrays or per-row calls.
- **Correctness**: scalar is the executable oracle; one exact /255 rounding
  formula; every provider passes exhaustive alpha/boundary, randomized,
  misaligned, tails, overlap, zero-length, cross-page, target-endian tests;
  register only bit-exact kernels.
- **Performance**: candidate must beat selected scalar by ≥10% in its bucket
  with acceptable p95, else the table keeps scalar; calibration cached by CPU
  model + ABI version + kernel hash + power profile; deterministic mode uses
  a certified table.
- **Threading**: one persistent pool/session; exclusive output tiles/bands;
  no shared cache lines; paint order within tile; scalar below measured
  dirty-area threshold; separable filters; scroll = copy + exposed damage.

## 6. GPU plan + backends (lanes G0–G4)

- **G0 common plan** `GpuRenderPlan {passes, batches, uploads, transients,
  capability_key}`; common optimizer does instances, batching, indirect args,
  dirty-range uploads, dependencies, transient lifetimes, residency.
  Backends only encode.
- Persistent session per backend: device/queue, swapchain, allocators, 2–3
  frame contexts, upload rings, pipeline cache, descriptor/argument
  allocator, atlases, transient heap, sync objects. Warm frames never:
  recreate device/pipelines, allocate a full framebuffer, device-idle, read
  back, or submit per-widget.
- **G1 Vulkan**: early persisted pipelines + VkPipelineCache per device
  identity; frame command pools + staging rings; dirty tiles into ≤2 command
  buffers; fences/timelines not wait-idle; exact barriers from the pass
  graph; dirty-range uploads only. (Host caveat on record: this dev host's
  QEMU cannot instantiate virtio-gpu-gl / Venus — E2/E3 stay parked; see
  `doc/08_tracking/bug/simpleos_vulkan_board_gap_venus_is_qemu_only_2026-08-06.md`.)
- **G2 Metal**: persistent PSOs + argument buffers, triple buffering, ~1
  command buffer/frame, heaps for proven-disjoint transients, GPU-resident
  textures, no CPU mirror of GPU-only surfaces.
- **G3 D3D12**: immutable PSO cache, persistent shader-visible descriptor
  heaps (suballocate; heap switches bounded), per-frame allocators + upload
  rings, batched precise barriers, pipeline-library persistence.
- **G4 route modes**: keep the existing `cpu_selected` vs `gpu_fallback`
  receipt contract (`draw_ir_v3_execution_route.spl`) and add CPU
  subconfiguration under it:

```
render:
  mode: cpu_reference          # cpu_reference | hybrid_vector_gpu | resident_gpu
  cpu:  {vector: auto, threads: auto, calibration: cached, deterministic: false}
  gpu:  {backend: auto, frames_in_flight: 3}
  verification: {shadow_frames: 30, exact_integer_pixels: true}
```

Forced ISA/backend fails closed if unavailable; `auto` states its reason in
the receipt.

## 7. WM / GUI / Web / events adoption (lanes U0–U3)

- **WM**: window = stable ID+generation, property-tree nodes, retained chunk
  range, optional cached backing surface, damage region, event-owner record.
  Move = update transform + damage old/new + recompose cache + repaint only
  exposed. Replace production PPM/file transport with slot-backed shared
  surfaces / shm ring / direct compositor references; PPM = test/export only.
- **GUI**: depends on `Draw2DSceneService` (begin_update → DirectSceneWriterV2
  → commit_update → SceneDeltaRef), not Engine2D concretes. Widgets update
  retained component ranges; GUI-hosted Web gets a sublease in the same arena.
- **Web style**: `PropertyId: u16` enum (append-only, generated),
  `Declaration {property, value_id, flags}`, `ComputedStyleHot` (display,
  position, visibility, opacity, color/background IDs, width/height value
  IDs, layout/paint flags) + cold side table. `apply_declarations` iterates
  only existing declarations — O(k). Parse names→PropertyId once, values→
  typed once; intern immutable computed styles; selector indexes +
  invalidation sets; containment where semantics allow; CSS logical units
  stay distinct from device-pixel layer-eq types; DrawIR deltas only for
  affected components; shaped-run + glyph caches.
- **Events**: keep the preallocated ring; make the whole path allocation-free.
  One POD `InputPacket`; Host/Wm/Gui/Web views only where representation and
  units are identical (host→web coordinate transform is an explicit property-
  tree op, not a view). Routing: ring → batch → one hit test on the DrawIR
  hit-shape index → `RouteToken {scene_generation, owner_id,
  owner_generation, path}` → owner chain → handler. `drain_into(batch)` not
  allocating `drain()`; SPSC power-of-two rings, release/acquire; coalesce
  move/wheel, never down/up/key/text/focus/close; reject stale generations;
  AOP only at batch boundaries.

## 8. Allocation and capacity model

Four classes: session-persistent (arena, atlases, pipelines, pool), frame
arena (plan nodes, dirty ranges), per-thread scratch (coverage, filter rows),
GPU ring/heap (fence-delimited). Steady-state invariants:

```
heap_allocations_per_warm_frame   = 0
scene_copy_bytes                  = 0
full_frame_readback_bytes         = 0
pipeline_creations_per_warm_frame = 0
descriptor_heap_switches          = bounded
event_allocations                 = 0
```

Capacity: high-water marks + EWMA + retained p99 per table; configured
headroom; refuse or schedule rebase on overflow; grow only at safe frame
boundary; never mid-emission; fixed-capacity low-memory mode for SimpleOS.
Enforced by C4's `@noalloc @copy_budget(0) @bounded_loop` MIR verifier.

## 9. Parallel-agent waves

Discipline carried over from the screens plan: exclusive path ownership,
count-based verdicts, deliberate sabotage tests, one integration owner for
shared registry/switch files.

```
C0 → C1 → C2 → C3 → C4          (compiler lane; C5 integration owner)
F0 ─────────────────────────┐
F1 → F2 → F3 ───────────────┼→ O0..O4 → placement
W0 ─────────────────────────┘        ↓
                        CPU lanes (P0..P5)   GPU lanes (G0..G4)
                                 └────────┬────────┘
                            WM/GUI/Web adoption (U0..U3, U4 cutover)
                                          ↓
                            parity/perf promotion (V0, V1)
```

Wave 0 (foundation): F0 perf-receipt v2 + engine-identity fail-closed gate;
F1 class identity; F2 span ABI; F3 arena V2; F4 presentation audit (no normal
readback); W0 web O(k) declarations. **F1→F2→F3 is the performance critical
path.** Wave 1: C0–C5. Wave 2: O0 revisions, O1 property trees/chunks, O2
damage/tiles/occlusion (sabotage: mark translucent opaque → gate must go
red), O3 resources/text, O4 placement/registry. Wave 3A CPU: P0 scalar
oracle+registry, P1 x86, P2 Arm, P3 RISC-V, P4 scheduler/filters, P5 sole
provider-aggregation owner. Wave 3B GPU: G0 plan (CPU mock encoder proves
deterministic command plan), G1–G3 concurrent after G0 freezes, G4 selection.
Wave 4: U0 GUI, U1 Web deltas, U2 WM cached surfaces + transform-only move,
U3 events, U4 flag-guarded cutover at one dispatch site, V0 differential/
property suites (no vacuous all-zero pass; sabotage required), V1 promotion.

## 10. Test matrix and gates

Workloads: 320×240 / 1080p / 4K / 8K × damage {0, 0.1, 1, 10, 100}% × scenes
(solid, mixed widgets, text-heavy, scrolling, window move, image scale,
translucent overlays, rounded clips, gradients, blur/shadow, Web-in-GUI-in-WM,
event storm) × identities (interpreter/seed = correctness only; pure-Simple
AOT, x86/AArch64/RISC-V native, Vulkan/Metal/D3D12, SimpleOS/QEMU, target SBC
= performance).

Frame receipt metrics: stage times (style/layout/delta/opt/plan/raster/
present) + semantic_nodes_touched, style_properties_applied,
draw_rows_written, scene_copy_bytes, dirty/rasterized_pixels, culled/
occluded_ops, kernel_calls, ffi_calls, allocations, upload/readback_bytes,
gpu_submits, pipeline_creations, descriptor_heap_switches, glyph/tile cache
hits, forwarding_physical_hops, layer_view_copy_bytes, event_allocations.

Blocking correctness: scalar authoritative; ISA variants byte-identical; GPU
integer primitives byte-identical where representable; per-op (not global)
filter tolerances; old/new shadow parity; nonzero-pixel proof (two empty
buffers cannot pass); stale generations fail closed; unmet preconditions
disable the optimization, never approximate.

Blocking structural (warm): the §8 invariants, plus GPU submits ≤2/frame,
dispatch ≤1/prepared batch, style work O(declarations), idle raster pixels =
0, idle scene rows rewritten = 0.

Promotion: ≥10% p50 win in bucket, p95/RSS inside budget, genuine execution
proven by counters, no hidden fallback. Expectations: Simple AOT scalar
approaches C scalar (vs today's 31x, diagnosis claim 2); SIMD beats scalar
for large spans or stays unselected; 1% dirty ⇒ ≤5% full-frame raster bytes;
transform-only move ⇒ zero repaint; repeated text ⇒ zero shaping/raster/
upload; 8K80 claims only per declared damage class on specified hardware.

Sabotage tests (each lane breaks one invariant, proves its gate reds):
value-copy class assignment; allocating MutSpan; restored writer-local
arrays; css-px-as-device-px layer_eq; surviving forwarding wrapper in MIR;
allocation under @noalloc advice; translucent-marked-opaque occlusion;
AVX2 rounding change; vkDeviceWaitIdle; stale event-owner accepted; restored
wide property probing. A gate green under sabotage has proven nothing.

## 11. Execution order

1. F0 receipts + engine-identity gates. 2. F1 class semantics. 3. F2 span
ABI. 4. F3 direct writers. 5. F4 kill normal-frame readback/PPM. 6. O0–O2
revisions/damage/chunks. 7. W0 O(k) styles. 8. P0 scalar batch oracle.
9. P1–P3 ISA providers behind per-op dispatch. 10. G0 then G1–G3.
C-lanes proceed concurrently with 2–7 (existing aliases can be represented
as typed forwarding nodes internally before the new syntax lands).

Explicitly avoided: new GuiIR/WebIR; runtime wrapper per layer; per-widget/
glyph/tile GPU submits; per-row FFI with gather/scatter; full readback for
presentation; one global widest-SIMD decision; implicit coordinate/unit/
color/alpha/host-device conversions; optional aspect fields in core objects;
per-pixel dynamic AOP; perf claims from interpreter/seed; enabling an
optimization because a capability bit exists.

## 12. Reconciliation with screens workstreams (A–E)

| Screens item | Status vs this plan |
|---|---|
| WS-D damage tracking (`backend_software.spl`, zero consumers) | **Superseded in mechanism** by O2/§4-pass-4; the D3 investigation's finding (per-op `present()` clears damage; `get_pixel_buffer()` is a live alias) is a *precondition defect* F4 must fix before any consumer is wired. See `ws_d3_damage_present_investigation.md` §9. |
| WS-D SIMD env knob (`SIMPLE_2D_SIMD=auto|off|…`) | **Superseded** by P0–P5 per-operation kernel table; the knob survives as the `render.cpu.vector` config surface only. |
| WS-D occlusion culling (landed, 21/21 + 10/10) | Feeds O2; keep as the compositor-level conservative baseline. |
| WS-B ScreenHost/showcase, WS-C input HAL | Unchanged; U3 builds on WS-C's ring + `HostInputEvent` (already POD-shaped). |
| WS-E Vulkan | Unchanged and still blocked on this host (Venus gap bug); G1 defines the target contract it will adopt. |
| WS-A config/evidence | Unchanged; F0's receipt v2 extends (not replaces) the multiconfig evidence rows. |
