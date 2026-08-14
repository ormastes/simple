# Render-Perf / WM Hardening — Replan for Parallel Agent Teams (2026-08-07)

## 2026-08-14 restart12 replacement lane (canonical active slice)

This bounded lane supersedes the stale binary-provenance and bootstrap-blocker
statements below for the remaining sparse DrawIR performance work.  It does not
rewrite the historical T1--T20 record.

Current starting point: `release/x86_64-unknown-linux-gnu/simple` is a deployed
pure-Simple CLI and advertises direct `simple <file.spl>` and `simple -c`
execution.  The retained 2026-08-13 report predates this artifact and records
both forms failing with `missing command`; that result must be revalidated once,
not assumed current.  The native operation harness already proves a 1% retained
damage primitive p95 below 12.5 ms, while full-frame CPU repaint remains outside
budget.  The missing evidence is the self-hosted sparse DrawIR entry closure.

Acceptance items for this lane:

- [x] WARN: the deployed self-hosted CLI was tested once; minimal `-c` and the
  canonical entry both exit 248 before compiler receipts, without seed fallback.
- [ ] BLOCKED: the benchmark cannot start because source execution exits 248
  and cached native-build exits 0 without an artifact. It must still complete
  its 20-frame 7680x4320, 256x128 dynamic-damage
  corpus and emits backend, revision, considered/culled, readback, checksum,
  p50/p95, and receipt-validity fields.
- [ ] BLOCKED: correctness receipts must prove two considered and 512 culled commands per
  frame, nonzero readback, zero full-frame mismatches, and stable checksum.
- [ ] BLOCKED: executor p95 must be at most 12.5 ms and outer maximum RSS retained. This
  is an executor-only result and must not be described as presentation or
  physical-scanout proof.
- [x] N/A: no `.spl` files were changed, so no touched source requires the O3
  optimizer inspection; documentation and direct-env guards still run once.
- [x] WARN: the final report names binary/source revision, attempted mode, viewport,
  readback mode, fallback state, p50/p95, RSS, and checksum proof.
- [ ] Intentional changes are committed, rebased under
  `/tmp/simple-main-restart12-push.lock`, pushed as `HEAD:main` without token
  environment overrides, and proven reachable from the refreshed origin/main.

Current blockers and allowed terminal verdicts:

- A self-hosted dispatcher/entry-closure failure is an implementation blocker,
  not render timing; fix it within three verify/fix cycles or finish WARN with a
  concrete tracking record and retained failing command evidence.
- Host OOM/watchdog before receipts is WARN and keeps 8K/80 unproven.  A smaller
  viewport, bootstrap interpreter, native C-only harness, cached replay, or
  software-fallback substitution cannot satisfy this slice.
- Full-frame CPU repaint is already measured outside budget and is not rerun by
  this lane; the accepted workload is exact sparse retained damage.

Verification is single-pass per acceptance item, with at most three total
fix cycles.  Convergence ends the lane.

Supersedes the scheduling half of
`doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md` §9/§11 (the
architecture in §1–§8 of that plan stands unchanged). Supersedes the status
tables in `doc/09_report/ui/perf/render_perf_campaign_status_2026-08-06.md`,
which was written mid-session and is stale on four rows (corrections in §1).

Purpose: a future session must be able to launch N agents **at once** off this
doc without further scoping and without collisions. §3 is the operative part.

Status legend (unchanged): **DONE** (implemented + verified + sabotage-proven) ·
**PARTIAL** (real progress, explicit gap) · **DESIGNED-ONLY** · **BLOCKED**
(explicit reason) · **NEEDS-INVESTIGATION** (open correctness question).

Binary provenance for every result cited: `bin/simple` →
`bin/release/x86_64-unknown-linux-gnu/simple` = the **Rust bootstrap seed**. No
number in this campaign is a pure-Simple AOT measurement. `bin/simple build
bootstrap` has an open Stage-3 blocker (`.claude/rules/bootstrap.md`), so any
claim requiring a self-hosted binary is gated on an isolated bootstrap window.

**Sabotage targets are unverified.** Where a unit below names a sabotage
target (a function/line to stub or invert to prove a spec is real), that
target was derived from expected structure, not a grepped call chain — the
sibling plans in this campaign have each had at least one named target turn
out wrong or nonexistent on verification. Grep the real call chain before
executing a sabotage step, and correct the unit inline (with a note) if it
disagrees.

---

## 0. Corrections to the previously-believed state

Recorded here because acting on the stale version would waste an agent's pass.

| Previously believed | Verified truth (2026-08-07) |
|---|---|
| C0–C5 **M2 LANDED** (`6d65d7d7142d`, "feed layer_eq_checker real compute_struct_layout output") | **PARTIAL.** That commit is `test(compiler):` and adds **only** `test/01_unit/compiler/semantics/layer_eq_checker_real_layout_spec.spl` (+171, 1 file). Production `layer_eq_checker.spl` still consumes **declared** `LayerEqType`/`LayerEqField` facts — the design doc's §6 item 3 ("offsets/sizes come from declared layouts, not real compiler layout") is still open. M2 is spec-side only. |
| Bucket gate lives in `src/lib/nogc_sync_mut/gpu/engine2d/backend_software.spl` | **That path does not exist.** Real file: `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl`, `ensure_kernel_table()` at :813, bucket probes :831-834. Also: only **`fill_const`** is gated — no blend/copy/src_over op is probed at all. |
| `style_block.spl` still does wide property probing (the thing W0 exists to kill) | **Already O(k)-ish by a different route.** `style_block.spl` (547L) has a landed selector index (`build_selector_rule_index` :211, `selector_index_candidates` :248) and its cascade does exactly **two** string compares total (:322, :332), not an if/elif chain. W0's `style_property_id.spl` is still unwired, but the win it was scoped to capture is partly already banked — re-measure before assuming a large delta. |
| `host_wm.spl` under `src/lib/nogc_sync_mut/ui/` | Real path `src/app/ui_showcase/hosts/host_wm.spl:84-104`. F4's PPM-per-frame write **and** the per-pixel `rt_ptr_read_i64` loop at `src/lib/common/ui/window_scene_draw_ir.spl:522-536` are both **still unfixed**. |
| Blend-span kernels are C + Rust bridge + `.spl` wrappers | Confirmed, plus an unstated fact: `5f19c774648` **also touched the Rust seed** (`interpreter_extern/simd.rs` +86, `mod.rs`, `common/runtime_symbols.rs`). Nothing references the new C symbols from any build file — only the `.c` file itself is listed in `src/compiler_rust/runtime/build.rs:137,307`. Unreachable until a full bootstrap. |

All 19 commit SHAs in the session hand-off list were verified to exist and to
carry the described subject line. Only the M2 *scope* claim was wrong.

---

## 1. Current-state table by lane

### F — foundation / packed memory path

| Item | Status | Evidence |
|---|---|---|
| F0 engine-identity gate | DONE (as convention) | Every report in this campaign carries a binary-identity block |
| F1 class-field reference semantics | **BLOCKED (no fix location)** | `doc/08_tracking/bug/class_field_reference_semantics_diverge_2026-08-06.md` — "Investigated, not fixed (blocked)". Re-verified live: JIT yields REF and core-dumps on an Option-class field; interpreter COPYs. Root cause is in the out-of-scope Rust seed. **Mitigation is already applied** in `src/lib/nogc_sync_mut/ui/draw_ir_v3_native_writer.spl:14-25` (explicit "captured BY VALUE" note; owning locals; commit via free functions taking arena+writer as fresh parameters) |
| F2 packed-pixel basis (`rt_typed_words_u32`) | **BLOCKED (premise refuted)** | `rt_typed_words_u32_is_not_a_packed_pixel_basis_2026-08-06.md` — 8-byte stride, no surface built. The new blend kernels do **not** supply an accidental basis: they are scalar unbox/rebox over boxed `int64_t` despite the "SIMD" name. Only surviving lead: `RT_CORE_ARRAY_FLAG_BYTES` / `rt_typed_bytes_u32_le_at/set`, unwired to any `.spl` surface → scoped as **T6** |
| F3 arena V2 | **PARTIAL** | `src/lib/nogc_sync_mut/ui/ui_scene_column_arena_v2.spl` (196L) and `draw_ir_v3_direct_writer_v2.spl` (42L) exist. `src/lib/common/ui/ui_scene_delta_v2.spl` and `ui_scene_ports_v3.spl` — **absent**; `SceneDeltaRef` has no home → **T5** |
| F4 presentation readback | **PARTIAL — unfixed** | `host_wm.spl:84-104` PPM bytes + checksum written per frame; `window_scene_draw_ir.spl:522-536` per-pixel `rt_ptr_read_i64` while-loop over the whole buffer → **T3**, **T4** |
| JIT closure Defect 2 (named-fn-as-value silent miscompile) | **GUARDED (2026-08-07)** | `jit_closure_abi_refuses_lambdas_and_miscompiles_fn_refs_2026-08-06.md` § "T7 landed" — `first_named_fn_value_load` in `src/compiler_rust/compiler/src/codegen/jit.rs` refuses the module, matching Defect 1's loud fallback; ABI itself still unfixed → **T7 DONE** |

### W — CSS / style hot path

| Item | Status | Evidence |
|---|---|---|
| W0 PropertyId + Declaration + `apply_declarations` | **PARTIAL — orphaned** | `fa7954d1eca`; `src/lib/gc_async_mut/gpu/browser_engine/style_property_id.spl` (8.9 KB): `property_id_from_name` :55, `class Declaration` :88, `declaration_from_name_value` :112, `apply_declarations` :141. Referenced **only** by `test/01_unit/lib/gc_async_mut/gpu/browser_engine/w0_property_id_declarations_spec.spl`. Zero `src/` importers → **T1** |
| W1 `ComputedStyleHot` split | **NEEDS-INVESTIGATION** | Spec exists (`computed_style_hot_split_spec.spl`); no verified pass/fail, no production consumer confirmed → **T2** |
| W2 selector index | **DONE (mechanism) / uncommitted** | `style_block.spl:211,248,72,309`. **File is `M` in this shared tree from another session** — collision hazard, see §3 |
| §7 DrawIR deltas | **DONE** | `0502c2b7873`; `src/lib/common/ui/render_opt/draw_ir_delta.spl` (103L) + spec, 5/5 incl. sabotage |
| §7 shaped-run cache | **DONE** | `c1e232a9a1e`; `src/lib/nogc_sync_mut/text_layout/font_renderer.spl:145-159`, accessors :264/:267 |
| §7 glyph-raster cache | **DONE** | `font_renderer.spl` — cross-instance cache in `get_glyph`, push inline in the method body per T11's boundary finding (not a revert of any prior diff — none existed to restore). Spec: `test/01_unit/lib/common/text_layout/glyph_raster_cache_spec.spl`, 4/4, sabotage-verified. Nonzero hit rate confirmed on both `bin/simple run` (JIT) and the interpreter test lane → **T12** |

### C0–C5 sub-lane (zero-cost layers) — see also the M-milestone doc

| Milestone | Status | Evidence |
|---|---|---|
| M0 layer DAG + `layer`/`uses` parsing + real compile errors | **DONE** | `e31cb8287393` (`35.semantics/layer_dag_checker.spl`, 150L), `8bf932d3f8d7` (soft-keyword parsing), `37eeb0b54bce` (wired to real compile errors) |
| M1a `@layer(NAME)` module tagging | **DONE** | `0cea0bb7dbe7` — `ParserModule.tagged_layer` |
| M1b call-direction check | **DONE, WARN-level** | `e1f9ed31a770` (`90.tools/verify/layer_call_scan.spl` 230L + `35.semantics/layer_call_direction_checker.spl` 183L), `eab9b5f9c5b5` (whole-program wiring in `driver_source_pipeline_parsing.spl`). Deliberately `eprint` not `add_error` — edge source is a bare-`ident(` text heuristic → **T13** promotes it |
| M2 real-layout wiring | **PARTIAL (spec-only)** | See §0. `6d65d7d7142d` adds a spec only; `layer_eq_checker.spl` (189L) still reads declared facts → **T14** |
| M3 obligations 5–8 | **DONE** | `248291b5caa2` — `layer_eq_checker.spl` +109; all 8 obligations present |
| M4 `HirForwardDecl` | **PARTIAL (struct only)** | `56093d1d9d11` — `src/compiler/20.hir/hir_forward_decl.spl` (56L) + spec. **Referenced by zero passes**; `src/app/desugar/forwarding.spl` (504L text generator) is still authoritative → **T15** |
| M5/M6/M7 (C3/C4/C5) | **DESIGNED-ONLY** | Sequenced behind M4; `effect_verifier.spl` (385L) green on fixtures, unwired to real MIR |

### O / P / G / U / V

| Item | Status | Evidence |
|---|---|---|
| O0/O1 revisions + property trees | **DONE** (T9, 2026-08-07) | `gui_showcase_perf_source_revision_contract_spec.spl`: 3/3 (dropped an unsatisfiable `expect(code).to_equal(0)`, added sabotage control); `gui_web_2d_source_revision_emitters_spec.spl`: 3/3 (added sabotage control). Binary: `bin/release/x86_64-unknown-linux-gnu/simple` (seed), `--mode=interpreter`. Detail: `doc/08_tracking/bug/gui_showcase_source_revision_spec_asserted_wrong_exit_code_2026-08-07.md` |
| O2 damage / occlusion | **DONE** | V-lane suite: `compositor_occlusion_rect_spec.spl` 21/21, `compositor_occlusion_spec.spl` 10/10 (130.6 s — needs a 300–600 s per-spec timeout, not 150 s) |
| O3 rasterizer / resources | **PARTIAL** | `paint_chunk_rasterizer_spec.spl` (2 its), `widget_draw_ir_glyph_run_spec.spl` 4/4 |
| P0/P1 SIMD bucket gate | **DONE (honest negative)** | `6c048f9af5ce`; `backend_software.spl:813,831-834` probes TINY/SMALL/MEDIUM/LARGE. Honest result: **SIMD lost at every bucket under the interpreter; all four stayed scalar.** `_kernel_probe_fill_bucket:66,87-90` |
| P1 gate coverage beyond `fill_const` | **NOT STARTED** | Only `fill_const` is probed → **T10** |
| P2 blend-span kernels | **T16 RE-RUN (2026-08-07): premise refuted — root cause is NOT the bootstrap block** | `5f19c774648`, source only, 8 files/+329. `nm` on the deployed (still-seed) binary and on `libsimple_runtime.a` proves the two new C symbols are absent from the native ABI, while all 5 siblings are present. Root cause found: the working siblings are provided by a **second, independent Rust reimplementation** in `engine2d_simd_ops.rs` (`simple_runtime` crate), not by `runtime_simd_dispatch.c` (dead code for this link config, selective-archive-extraction). `engine2d_simd_ops.rs` never got the two new blend-span functions added — a plain Rust-crate fix, not a Stage-3/bootstrap issue. See `t16_blend_span_c_symbol_not_reachable_three_implementations_2026-08-07.md` |
| P — production call sites for registered SIMD kernels | **NEEDS-INVESTIGATION** | The V0/V1 "zero production call sites" finding was never confirmed closed → **T8** |
| G0–G4 Vulkan | **BLOCKED (board)** | virtio-gpu-gl / Venus is a QEMU-only device on this host; no physical-board path. Filed per `.claude/rules/board-runnable.md` (`simpleos_vulkan_board_gap_venus_is_qemu_only_2026-08-06.md`) |
| U0b hosted input | **DONE** | `hosted_input_sdl2_spec.spl` 28/28 |
| U2 WM/web showcase | **NEEDS-INVESTIGATION** | `wm_web_standards_showcase_child_frame_timeout_2026-08-06.md` Open — `bin/simple run` under `examples/**` has an internal 10 s watchdog (`DEFAULT_EXAMPLES_TIMEOUT_SECS`); past it the real verdict is FAIL (child-frame-timeout), not a hang → **T17** |
| U3 event allocation | **DONE (premise refuted)** | Path already allocation-free per event; `InputEventQueue.drain()` allocates but is dead code |
| U4 cutover sweep | **BLOCKED (no producer) — T20 verdict** | `t20_u4_cutover_sweep_2026-08-07.md` — the arena-V2/`SceneDeltaRef`/packed-producer path has zero callers anywhere under `src/app/**`; `showcase_core.spl:286-289` is the one real dispatch site and never references it. No `DrawIrV3Scene`-equivalent output exists on the new path to cut over TO → **T20 (investigation-only)** |
| V0/V1 promotion suite | **T19 RE-RUN: RED (contention, not regression)** | 10/11 specs GREEN, 168/168 examples, 1 `CANNOT_EXECUTE` (occlusion spec timed out at 600s under load avg 39.6) → bug doc filed |
| Test-harness fixes (daemon binary shadowing; `slow_it` floor) | **DONE** | `423c0c46b83` + the `simple_binary()` fallback-order fix; these retroactively explain most "timeout" findings in this campaign |
| gui_showcase exit-code contract | **NEEDS-INVESTIGATION** | `gui_showcase_perf_source_revision_contract_exit_code_never_zero_2026-08-07.md`, status open (residual, pre-existing, family-wide) → **T18** |

---

## 2. The three categories — do not confuse them

**(a) Executable now** — T1…T20 below. No unnamed prerequisite; an agent can
start any of them in the next session.

**(b) Blocked on a *specific, named* prerequisite** (the prerequisite is stated
and is itself achievable):

| Unit | Named prerequisite | What unblocks it |
|---|---|---|
| **T16** blend-kernel C-symbol verification | **REVISED 2026-08-07:** not actually gated on the bootstrap window — see `t16_blend_span_c_symbol_not_reachable_three_implementations_2026-08-07.md`. Needs `rt_engine2d_simd_blend_span_u32`/`_blend_const_span_u32` added to `src/compiler_rust/runtime/src/value/engine2d_simd_ops.rs` (plain Rust-crate change) | A normal seed rebuild once `engine2d_simd_ops.rs` gets the two missing functions, then re-run this unit's `nm` checks. The Stage-3 self-host blocker is orthogonal and does not need to be fixed first |
| **T12** land the glyph-raster cache | **T11** — fix the `[text]`-array read-back corruption under native/JIT | T11 landing with a passing repro |
| **T15** wire `HirForwardDecl` into a pass | Nothing external — but must not start before T14, or it wires against fixture-layout facts | T14 landing |
| Any claim of a *pure-Simple AOT* perf number | Same Stage-3 bootstrap blocker | Same as T16. Until then, every number is seed-JIT/interpreter-bound and must say so |

**(c) Architecturally blocked, no known fix location — NO AGENT ASSIGNED.**
Standing note only. Do not spawn a unit against these; do not let a launcher
serialize other work behind them.

- **F1 class-field reference semantics.** Root cause in the Rust seed; no
  bounded fix location. **The workaround is already applied where it matters**
  (`draw_ir_v3_native_writer.spl:14-25`). Consequence for scheduling: units
  that touch mutable scene state are **not** blocked by F1 — they proceed under
  the workaround in §4.
- **F2 packed-pixel basis as premised.** Refuted; do not resume on the old
  premise. The one thing that could reopen it is carved out as **T6** (an
  investigation, not an implementation) — do not let that lead disappear into
  this note.
- **JIT closure Defect 2.** The ABI fix is unbounded. The *guard* is T7; the fix
  is not assigned.
- **G-lane real Vulkan/Venus board wiring.** QEMU-only device, no physical-board
  path. Filed per `.claude/rules/board-runnable.md`. Not an agent unit until
  hardware exists.

---

## 3. Parallel agent team assignments

### How to read a unit

Every file is tagged **[E]** existing / **[N]** new-to-create / **[E!]** existing
**and currently uncommitted in this shared tree by another session**. Two units
creating **[N]** files in the same directory do **not** collide; two units
editing the same **[E]** file **do**.

**Collision sets are symmetric** — if Tx lists Ty, Ty lists Tx. A launcher may
run any set of units with pairwise-disjoint collision sets simultaneously.

**`SERIAL-BOOTSTRAP`** is a *global* mutex, not a pairwise collision: there is
one `bin/simple`, so a unit carrying this tag must run alone with respect to
every other unit that builds or redeploys a binary.

**`[E!]` protocol:** before touching an `[E!]` file, run `git status --short`
and `git diff origin/main -- <path>`. If it is still dirty from another session,
**do not touch it** — check the diff-growth to see if it is live
(`reference_probe_after_sibling_agent_edit_measures_their_fix`), and either wait
or re-scope. Never sweep another session's uncommitted work into your commit.

---

### WAVE 1 — 11 units, all executable now, no inter-wave dependencies

**T1 — Wire W0 PropertyId/Declaration into the live cascade**
- Goal: make `style_block.spl`'s cascade consume `apply_declarations` instead of
  its own ad-hoc property handling, so W0 stops being an orphan.
- Files: `src/lib/gc_async_mut/gpu/browser_engine/style_block.spl` **[E!]**;
  `src/lib/gc_async_mut/gpu/browser_engine/style_property_id.spl` **[E]**.
- Spec: extend `test/01_unit/lib/gc_async_mut/gpu/browser_engine/w0_property_id_declarations_spec.spl`
  with a *cascade-level* case (declarations applied through the real
  `style_block` path, not the module in isolation).
- Acceptance: a counter or spec proves the cascade reaches
  `apply_declarations`; sabotage = make `apply_declarations` a no-op, the new
  case must go red. **Measure before/after** — per §0 the cascade is already
  only 2 string compares, so state the honest delta even if it is ~0.
- Depends on: none. Collision set: **{T2}** (both touch `style_block.spl`), plus
  the `[E!]` protocol.

**T2 — Verify/complete the `ComputedStyleHot` hot/cold split**
- Goal: turn W1 from "a spec exists" into a verdict, and give it a production
  consumer or delete it per "implement or delete".
- Files: `src/lib/gc_async_mut/gpu/browser_engine/computed_style*.spl` **[E]**,
  `style_block.spl` **[E!]** (consumer wiring only).
- Spec: `test/01_unit/lib/gc_async_mut/gpu/browser_engine/computed_style_hot_split_spec.spl` **[E]**.
- Acceptance: recorded pass/fail with binary provenance; if no production
  consumer exists after this unit, the unit's deliverable is an explicit
  delete-or-wire decision, not a PARTIAL.
- Depends on: none. Collision set: **{T1}**.

**T3 — Kill the per-pixel FFI readback (F4a)**
- Goal: replace the `rt_ptr_read_i64` per-pixel while-loop with a bulk/span read.
- Files: `src/lib/common/ui/window_scene_draw_ir.spl:522-536` **[E]**.
- Spec: new `test/01_unit/lib/common/ui/window_scene_readback_spec.spl` **[N]** —
  asserts output bytes identical to the per-pixel path AND that the FFI call
  count drops (counter-backed, not timing).
- Acceptance: byte-identical output + a counted FFI-call reduction; sabotage =
  return a zero buffer, the byte-equality case must go red (a nonzero-pixel
  proof is mandatory — two empty buffers must not pass).
- Depends on: none. Collision set: **{T4}** (functionally adjacent — T4 consumes
  T3's output shape; run them serially if both edit the readback signature,
  otherwise disjoint files).

**T4 — Take PPM off the warm frame (F4b)**
- Goal: `host_wm.spl` must not write PPM bytes + checksum every frame; PPM
  becomes test/export-only behind an explicit flag.
- Files: `src/app/ui_showcase/hosts/host_wm.spl:84-104` **[E]**.
- Spec: new `test/01_unit/app/ui_showcase/host_wm_present_no_ppm_spec.spl` **[N]**
  — warm-frame PPM writes = 0, export-mode writes = 1.
- Acceptance: counter proves 0 file writes on a warm frame; sabotage = re-enable
  the unconditional write, spec goes red.
- Depends on: none. Collision set: **{T3}**.

**T5 — Give `SceneDeltaRef` a home (F3 completion)**
- Goal: create the two missing F3 files so `SceneDeltaRef` and the v3 ports exist
  as the redesign plan §2 specifies.
- Files: `src/lib/common/ui/ui_scene_delta_v2.spl` **[N]**,
  `src/lib/common/ui/ui_scene_ports_v3.spl` **[N]**; read-only reference to
  `src/lib/nogc_sync_mut/ui/ui_scene_column_arena_v2.spl` **[E]**.
- Spec: `test/01_unit/lib/common/ui/ui_scene_delta_v2_spec.spl` **[N]**.
- Acceptance: `SceneDeltaRef` round-trips dirty ranges and refuses a stale
  `scene_generation`; sabotage = accept a stale generation, the refusal case
  goes red. **Producer IDs must be arena-absolute, never producer-local**
  (standing lesson).
- Depends on: none. Collision set: **{}** (all new files).

**T6 — Investigate: is `RT_CORE_ARRAY_FLAG_BYTES` a real 4-byte packed basis?**
- Goal: the *only* live lead that could reopen F2. Answer one question:
  do `rt_typed_bytes_u32_le_at` / `..._set` give a genuine 4-byte-stride packed
  pixel buffer reachable from `.spl`, or is this a second dead end?
- Files: read-only over `src/runtime/**`, `src/compiler_rust/runtime/**`; the
  deliverable is a doc, not code.
- Spec: none (investigation). Deliverable:
  `doc/08_tracking/bug/rt_typed_words_u32_is_not_a_packed_pixel_basis_2026-08-06.md`
  **[E]** gets an appended verdict section, or a new finding doc **[N]**.
- Acceptance: a stride measurement from a **running** probe (not from reading
  headers), plus an explicit YES/NO on `.spl` reachability. A "looks like it
  should work" is not an answer.
- Depends on: none. Collision set: **{}**.

**T7 — Loud guard for JIT Defect 2 (named-fn-as-value)** — **DONE 2026-08-07.**
Landed `Self::first_named_fn_value_load` in
`src/compiler_rust/compiler/src/codegen/jit.rs`; spec
`test/01_unit/compiler/jit_named_fn_ref_guard_spec.spl` (+ JIT probe) is
`Results: 3 total, 3 passed, 0 failed`; sabotage (guard removed) went RED
(test daemon timeout — the unguarded JIT calls a garbage function pointer).
Full evidence: `doc/08_tracking/bug/jit_closure_abi_refuses_lambdas_and_miscompiles_fn_refs_2026-08-06.md`
§ "T7 landed". Deployed binary md5 `8fb0a8781437b5cf37a2657611b0b1f0`.
- Goal: convert a *silent wrong answer* into a loud failure. Not a fix — Defect
  2's ABI fix is category (c).
- Files: wherever Defect 1's existing lambda guard lives (locate via the bug
  doc) **[E]**.
- Spec: `test/01_unit/compiler/jit_named_fn_ref_guard_spec.spl` **[N]** — a
  named-fn-as-value program must now fail loudly (or fall back), never return
  garbage silently.
- Acceptance: the pre-existing silent-miscompile repro from
  `jit_closure_abi_refuses_lambdas_and_miscompiles_fn_refs_2026-08-06.md` now
  produces a diagnostic; sabotage = remove the guard, the spec goes red.
- Depends on: none. Collision set: **{}**.

**T8 — Close the "zero production call sites for SIMD kernels" audit**
- Goal: answer definitively whether any registered SIMD kernel has a real caller
  in the production render path.
- Files: read-only grep across `src/lib/gc_async_mut/gpu/engine2d/**` and the
  render path; deliverable is an appended verdict in
  `doc/09_report/ui/perf/render_perf_v_lane_promotion_suite_2026-08-06.md` **[E]**.
- Acceptance: an enumerated call-site list (or an explicit empty list with the
  greps shown) — **anchor the greps** when counting a symbol class.
- Depends on: none. Collision set: **{}** (read-only over T9/T10's files; must
  be re-run after T10 if T10 lands first).

**T9 — Get a verdict on O0/O1 (revisions + property trees)**
- Goal: turn NEEDS-INVESTIGATION into DONE/PARTIAL with a real run.
- Files: `test/03_system/check/gui_showcase_perf_source_revision_contract_spec.spl` **[E]**,
  `gui_web_2d_source_revision_emitters_spec.spl` **[E]**.
- Spec: those two, run — plus any missing sabotage case added.
- Acceptance: recorded verdict lines with binary provenance; each spec has at
  least one sabotage case proving it is not vacuous.
- Depends on: none. Collision set: **{T18}** (T18 touches the same spec family's
  exit-code contract).

**T10 — Extend the honest bucket gate beyond `fill_const`**
- Goal: `ensure_kernel_table()` currently probes only `fill_const`. Extend the
  same probe-and-seal pattern to the other registered ops.
- Files: `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl` **[E]**
  (`ensure_kernel_table` :813, `_kernel_probe_fill_bucket` :66).
- Spec: extend `test/01_unit/lib/.../simd_span_batch_execute_spec.spl` **[E]**.
- Acceptance: each newly-gated op reports a per-bucket scalar-vs-SIMD verdict;
  an op that loses **stays scalar** and the doc says so. A gate that promotes
  everything is a failed unit. Sabotage = force `faster = true`, a correctness
  spec must go red.
- Depends on: none. Collision set: **{T8}** (T8 reads what T10 writes — if both
  run, T8 must re-run after T10).

**T11 — Fix the `[text]`-array read-back corruption**
- Goal: the named prerequisite for the glyph-raster cache. A minimal repro
  already exists in the bug doc.
- Files: located from the repro (array/text lowering) **[E]**.
- Spec: `test/01_unit/lang/text_array_index_readback_spec.spl` **[N]** — write
  then read back a `[text]` array under native/JIT **and** interpreter, both
  must agree.
- Acceptance: both engines agree; sabotage = revert the fix, spec goes red.
  State which binary ran it.
- Depends on: none. Collision set: **{}**.

---

### WAVE 2 — 6 units, each depends on a Wave-1 unit

**T12 — Land the glyph-raster cache**
- Goal: land what `c1e232a9a1e` deliberately withheld.
- Files: `src/lib/nogc_sync_mut/text_layout/font_renderer.spl:148-153` **[E]**.
- Spec: extend the shaped-run cache spec with glyph-raster hit/miss cases.
- Acceptance: nonzero hit rate under **both** engines (the original defect
  manifested as a zero hit rate); sabotage = disable the cache, hits go to 0.
- Depends on: **T11**. Collision set: **{}**.

**T13 — Promote M1b call edges from text heuristic to AST/HIR, then WARN→ERROR**
- Goal: `eab9b5f9c5b5` is deliberately WARN-only because edges come from a bare
  `ident(` text scan. Replace the edge source, then gate.
- Files: `src/compiler/90.tools/verify/layer_call_scan.spl` **[E]**,
  `src/compiler/35.semantics/layer_call_wiring.spl` **[E]**,
  `src/compiler/80.driver/driver_source_pipeline_parsing.spl` **[E]**.
- Spec: extend `test/01_unit/compiler/semantics/layer_call_wiring_spec.spl` **[E]**
  with the false-positive case the text scan gets wrong (a local fn sharing an
  imported symbol's name).
- Acceptance: that false-positive case passes under AST edges and would have
  failed under text edges — otherwise the unit proved nothing. Only then flip
  `eprint` → `add_error`. Also: cover the branches M1b skips
  (`parse_all_streaming_surfaces_impl`, native-entry-closure, `SIMPLE_BOOTSTRAP`)
  or state explicitly that they remain uncovered.
- Depends on: none technically, but sequence after T14 if both are launched (see
  collision). Collision set: **{T14}** (both in `35.semantics/`, and M2's
  registry feeds this).

**T14 — M2 for real: wire `layer_eq_checker` to `compute_struct_layout`**
- Goal: close the §0 correction. Production checker must read the compiler's own
  layout, not declared fixtures.
- Files: `src/compiler/35.semantics/layer_eq_checker.spl` **[E]** (189L),
  `src/compiler/30.types/type_layout.spl` + `_TypeLayout/layout_core.spl`,
  `arch_and_verify.spl` **[E]** (read/adapter only).
- Spec: `test/01_unit/compiler/semantics/layer_eq_checker_real_layout_spec.spl` **[E]**
  (currently spec-side-only — make it exercise the production path).
- Acceptance: **the load-bearing case is a compiler-inserted-padding difference
  that fixture-declared "same size" would have wrongly passed and real layout
  correctly fails.** If no such case exists, M2 has proven nothing beyond M1.
- Depends on: none. Collision set: **{T13}**.

**T15 — Wire `HirForwardDecl` into one pass (M4 plain-symbol phase only)**
- Goal: `56093d1d9d11` is a struct referenced by zero passes. Emit it for the
  simplest of `forwarding.spl`'s four phases (`fn name = target`), keeping the
  text generator live as fallback for the other three.
- Files: `src/compiler/20.hir/hir_forward_decl.spl` **[E]**, the HIR-lowering
  site **[E]**, `src/app/desugar/forwarding.spl` **[E]** (fallback selection
  only — do NOT delete it).
- Spec: extend `test/01_unit/compiler/hir/hir_forward_decl_spec.spl` **[E]** with
  a before/after **physical-hop count** for one plain-symbol forwarding site.
- Acceptance: hop count strictly decreases and the text-generated body is absent
  for that phase; the other three phases still route through
  `forwarding.spl` unchanged. Do not attempt field-path/trait/blanket phases in
  this unit.
- Depends on: **T14** (layer views must be proven against real layout before
  forwarding leans on them). Collision set: **{}**.

**T16 — Verify the blend-span C symbols are linked and bit-exact** — **RE-RUN DONE, RED (2026-08-07), premise refuted**
- Goal: `5f19c774648` landed source only. Prove the C symbol is linked, callable,
  and bit-exact against the scalar oracle.
- Files: `src/runtime/runtime_simd_dispatch.c` **[E]**, `src/runtime/runtime.h` **[E]**,
  `src/compiler_rust/runtime/build.rs` **[E]**, `simd_isa_provider.spl` /
  `simd_native_rows.spl` **[E]**.
- **Verdict:** run against the 2026-08-07 22:39 redeployed artifact
  (`bin/release/x86_64-unknown-linux-gnu/simple`, md5
  `70476ca038e184fecba4f910b0db9b18`). The redeploy is **still the Rust seed**
  (`bin/simple --version` prints the seed WARNING banner) — the task premise
  that this redeploy was a self-hosted build unblocking T16 does not hold, but
  T16's own acceptance bar (`nm` on the real artifact) is answerable
  regardless of seed-vs-self-hosted, and the answer is **NO**: `nm` shows
  `rt_engine2d_simd_blend_span_u32`/`_blend_const_span_u32` absent from both
  the deployed binary and `libsimple_runtime.a`, while all 5 sibling kernels
  are present as `T`. Root-caused (not inferred): the 5 working siblings are
  provided by a **second, independent Rust implementation** in
  `src/compiler_rust/runtime/src/value/engine2d_simd_ops.rs` (the
  `simple_runtime` crate, linked into the native ABI) — `runtime_simd_dispatch.c`
  is dead code for this link configuration (selective `-lstatic=runtime_sffi_c`
  extraction, nothing in the Rust crate graph references the C names). A
  standalone `gcc -c` of the C file confirms both new C symbols compile fine
  and would export as `T` if the archive member were ever pulled in — the gap
  is that `engine2d_simd_ops.rs` never received the two new functions, so
  there is no native-ABI provider at all, C or Rust. Full evidence (nm
  transcripts, archive-member-qualified `nm -A`, grep of all three
  implementation sites): `doc/08_tracking/bug/t16_blend_span_c_symbol_not_reachable_three_implementations_2026-08-07.md`.
- Spec: the verification suite planned in
  `doc/03_plan/ui/perf/engine2d_simd_blend_span_kernel_design_plan_2026-08-07.md` §5
  (bit-exact hashes, `sa==0` / `sa==255` / zero-length guards, two `describe`
  blocks) — **already implemented and run by a prior session** against the
  Rust interpreter bridge only (`simd_isa_provider_spec.spl:327-393`); that
  spec's own honesty note already documents it cannot reach the native/C path.
  Not re-run this session (no new coverage would result — the gap is a
  missing native-ABI function, not an unrun spec).
- Acceptance: the symbol resolves at link time (prove it — `nm`, not inference);
  every kernel is bit-exact vs scalar; a non-bit-exact kernel is **not
  registered**. State the binary provenance of the redeployed artifact.
  **NOT MET** for the native-ABI symbol (absent, not merely non-bit-exact);
  MET for the interpreter-bridge path (previously proven bit-exact, symbol
  presence re-confirmed in this binary).
- Depends on: ~~an isolated full-bootstrap window~~ **REVISED:** a plain Rust
  crate change to `engine2d_simd_ops.rs` + normal seed rebuild. The Stage-3
  self-host blocker (§2 category b, still open) is orthogonal to this fix.
  **Collision set: GLOBAL** — no other unit may build or redeploy concurrently
  (unchanged — a seed rebuild still needs exclusivity).

**T17 — Unblock the WM/web showcase child-frame timeout**
- Goal: the internal 10 s `DEFAULT_EXAMPLES_TIMEOUT_SECS` watchdog kills the
  driver before host/child finish loading, masking the real FAIL verdict.
- Files: the examples watchdog site **[E]**;
  `examples/**` WM/web showcase driver **[E]**.
- Spec/deliverable: a run that gets **past** the watchdog and records the real
  child-frame verdict; update
  `doc/08_tracking/bug/wm_web_standards_showcase_child_frame_timeout_2026-08-06.md` **[E]**.
- Acceptance: an actual verdict line (not a timeout) is produced. Note: an
  external `timeout` of any size does **not** help — the cap is internal.
- Depends on: none. Collision set: **{}**.

---

### WAVE 3 — 3 units, depend on Wave 1+2 landing

**T18 — Fix the family-wide gui_showcase exit-code contract**
- Goal: `gui_showcase_perf_source_revision_contract_exit_code_never_zero_2026-08-07.md`
  — the contract never returns 0, family-wide.
- Files: the showcase check driver + the affected `test/03_system/check/*` specs **[E]**.
- Acceptance: at least one member of the family exits 0 on success **and** a
  deliberately-broken member exits nonzero (both directions, or the fix is a
  fail-open).
- Depends on: **T9** (T9 establishes the family's real verdicts first).
  Collision set: **{T9}**.

**T19 — Re-run the V-lane promotion suite as a regression gate** — **DONE, RED-by-design (2026-08-07)**
- Goal: re-establish GREEN after Waves 1–2 and set the per-spec timeout for
  `compositor_occlusion_spec.spl` to 300–600 s (not 150 s, not 7200 s).
- **Verdict:** timeout narrowed from 1200s to 600s (top of the mandated band)
  in `scripts/check/check-render-perf-v-lane-suite.shs:64`. Re-run: 10/11
  specs GREEN (168/168 examples, 0 failed), 1 `CANNOT_EXECUTE`
  (`compositor_occlusion_spec.spl`, timed out at 600s) → **VERDICT: RED**.
  Root cause is real shared-WC contention, not a code regression: `uptime`
  showed load average 39.60 (5 concurrent agent sessions), ~3x the 14.0 load
  that previously required 1200s of headroom over this spec's ~130-140s clean
  baseline. Not silently widened back past the plan's 600s ceiling — filed as
  `doc/08_tracking/bug/v_lane_suite_occlusion_spec_times_out_under_shared_wc_contention_2026-08-07.md`
  with re-run (low-load) and permanent-fix unblock conditions. T16's
  blend-span kernels are not among this suite's 11 specs, so no explicit
  exclusion was needed for T16. Full Run 5 detail:
  `doc/09_report/ui/perf/render_perf_v_lane_promotion_suite_2026-08-06.md`.
- Files: the aggregate suite runner **[E]**;
  `doc/09_report/ui/perf/render_perf_v_lane_promotion_suite_2026-08-06.md` **[E]**.
- Acceptance: 11 specs, all examples, 0 cannot-execute, with binary provenance.
  A GREEN that includes a vacuous all-zero pass is a failed unit.
- Depends on: **all of Wave 1 and Wave 2**. Collision set: **{}** but must run
  last. **T16 must have completed (or been explicitly excluded) before Wave 3
  opens** — never run Wave 3 with a `SERIAL-BOOTSTRAP` unit in flight.
- **Degrade-explicitly rule (do not let this stall):** T16 is gated on a
  bootstrap window that may not be available, and T19→T20 transitively depend on
  it. If T16 remains blocked, **run T19 and T20 with T16 explicitly excluded**
  and have the suite verdict state, in words, that the blend-span kernels were
  not exercised and the C symbol remains unverified. A queued-and-stalled Wave 3
  is a worse outcome than a Wave 3 that names its own gap.

**T20 — U4 cutover sweep** — **DONE, investigation-only (2026-08-07)**
- Goal: the flag-guarded cutover at one dispatch site + the sweep confirming
  nothing else needs migrating.
- Files: the single dispatch site **[E]** — identify it first, do not pre-commit.
- Acceptance: an enumerated sweep list (what was checked, what needs nothing),
  not a prose "nothing else found".
- Depends on: **T3, T4, T5, T19**. Collision set: **{}**.
- **Verdict:** the premise does not hold. `showcase_core.spl:286-318`
  (`showcase_scene` + `showcase_run` → `host.present_scene(scene)`) is the
  one real dispatch site, and it is explicitly documented in-source as "the
  single production path; no host sees a writer." The candidate new path
  (`UiSceneColumnArenaV2` → T5's `SceneDeltaRef` → the three packed
  producers) has **zero callers under `src/app/**`** — grepped and
  enumerated, not assumed. There is no `DrawIrV3Scene`-equivalent output on
  the new path to flag-cutover TO; flipping a flag would route real hosts to
  a pipeline with no proven output, which is a regression, not a cutover.
  Full sweep table: `doc/09_report/ui/perf/t20_u4_cutover_sweep_2026-08-07.md`.
  No spec/sabotage — investigation-only per the plan's own rule. T19 was not
  yet landed on `origin/main` at the time this unit ran (collision set `{}`,
  and T19 only re-runs an already-GREEN suite per §1's V0/V1 row — no file
  T20 touches depends on T19's output).

---

### Launcher quick-reference

| Wave | Units | Safe to run fully in parallel? |
|---|---|---|
| 1 | T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 | Yes **except**: {T1,T2} serialise; {T3,T4} serialise if the readback signature changes; {T8,T10} serialise (T8 after T10); {T9,T18} — T18 is Wave 3 anyway. Honour the `[E!]` protocol on `style_block.spl`. Max concurrency ≈ 8 |
| 2 | T12 T13 T14 T15 T16 T17 | {T13,T14} serialise; T15 after T14; **T16 runs ALONE** (SERIAL-BOOTSTRAP). Max concurrency ≈ 4 when T16 is not running. **T16 must finish or be formally excluded before Wave 3 opens** |
| 3 | T18 T19 T20 | T18 ∥ nothing else needed; T19 then T20, strictly ordered. If T16 was excluded, T19/T20 still run — see T19's degrade-explicitly rule |

---

## 4. Standing conventions every agent team must follow

Distilled from what actually worked this session — each of these caught a real
false result.

1. **Sabotage-test every correctness claim.** Break the invariant, prove the gate
   reds, revert. A gate green under sabotage has proven nothing. This is the
   single convention that caught the most vacuous passes this session.
2. **State binary provenance on every spec result** — seed
   (`src/compiler_rust`) vs self-hosted (`src/compiler/`). `bin/simple test`
   silently delegates to the seed and reports green while `.spl` changes sit
   inert (`reference_simple_test_silently_delegates_to_seed_child.md`). Say
   which binary ran, every time, without being asked.
3. **No perf claim from the interpreter or the seed.** The honest P0/P1 result —
   "SIMD lost at every bucket, all stayed scalar" — is worth more than a
   promoted kernel backed by an interpreter number.
4. **Verify the diffstat matches your intended file list before pushing.**
   `git diff --stat $BASE $NEWCOMMIT` must show *exactly* your files. Never
   `git add -A`.
5. **Run all three pre-push guards** (`check-no-conflict-tree-push.shs`,
   `check-no-conflict-markers-push.shs`, `check-tree-size-push.shs`) from the
   repo root of a real clone, and read the verdict line — `ERROR — nothing was
   checked` (exit 2) is not a pass.
6. **This working tree is shared with other concurrent sessions.** Never
   bulk-commit files you did not author. Before touching any `[E!]` file, check
   `git status --short` and diff growth; a file another session is mid-flight on
   is off-limits.
7. **Mutable state: pass by parameter, never store into a field or array slot.**
   The standing F1 workaround, applied and proven in
   `draw_ir_v3_native_writer.spl:14-25`. Keep the mutable instance in one owning
   local; commit via free functions taking it as a fresh parameter. This is not
   optional style — it is the only reason the arena writer is engine-stable.
8. **No enums on hot paths**, and never call `Dict.len()` or `.get()` on a dict
   whose value type is a struct/class/enum under native codegen
   (`doc/07_guide/language/dict_native_pitfalls.md`).
9. **Land the smaller honest slice over a forced completion.** Every deliberate
   non-landing this session (glyph-raster cache, blend-kernel redeploy) was the
   right call and is why the state above is trustworthy. File the gap as a named
   follow-up; never silently normalise a workaround.
10. **Nonzero-pixel proofs are mandatory** for any raster/readback claim — two
    empty buffers must not be able to pass.
11. **Anchor your greps when counting a symbol class**, and prefer a positive
    capability probe over a version banner when establishing binary identity.
12. **Push each landed unit to GitHub immediately**, per unit, not batched.

---

## 5. Relationship to other plans

- `render_perf_redesign_plan_2026-08-06.md` — architecture §1–§8 unchanged and
  authoritative; §9/§11 scheduling replaced by §3 here.
- `zero_cost_layers_c0_c5_staged_implementation_plan_2026-08-07.md` — M-milestone
  detail; T13/T14/T15 here are its M1b-promotion, M2, and M4 slices.
- `engine2d_simd_blend_span_kernel_design_plan_2026-08-07.md` — T16's spec source.
- `engine2d_simd_fill_span_colour_boxing_fix_plan_2026-08-07.md` — carries the
  **retraction** (`4d2feb50db5`): the pixel-boxing "corruption" was a hex→decimal
  error in the original doc, not a defect. Do not re-open it.
- `.claude/rules/board-runnable.md` — governs the G-lane exclusion in §2(c).
