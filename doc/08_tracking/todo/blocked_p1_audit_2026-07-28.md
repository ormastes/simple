# Blocked "P1" audit — 2026-07-28

Evidence-based re-verification of every tracked item carrying a blocked-class
status. Nobody had audited these; this file records what was actually checked.

- **Auditor:** automated audit pass, 2026-07-28
- **Tree audited:** `HEAD = 0b98a9ea24d96778eae4b6d02beb73c5aca6217b`
- **origin/main at audit time:** `5151659192b05a22f2aca175347d57bcddada790`
- **Scope rule:** owned code only; vendored runtime excluded.

> This directory's `README.md` calls itself deprecated, but it is still in
> active use (`rendering_performance_historical_regression_baseline_2026-07-27.md`
> landed here in `1803212fb36`), and this audit was explicitly scoped to it.

---

## 0. What "22 P1 blocked" actually is

The reported figure was approximate and its priority half is **not supported by
the data**.

**Count.** The population is **exactly 22**, defined reproducibly as bug files
under `doc/08_tracking/bug/` whose Status / Verdict / State / Classification
line carries a blocked-class value:

```sh
grep -rliE '^\s*[-*]?\s*\**(status|verdict|state|classification)\**\s*:?\s*.{0,80}blocked' \
  doc/08_tracking/bug/*.md | wc -l
# => 22
```

**Priority.** 21 of those 22 files contain **no priority token at all**
(checked with `grep -ioE '\bP[0-3]\b'` per file). Only
`native_build_worker_zombie_parent_hang_2026-07-03.md` mentions P1. So "22 P1
items" conflates a count of blocked items with a priority that was never
recorded. Treat the population as "22 blocked items", not "22 P1 items".

**Other trackers do not corroborate a blocked-P1 backlog either:**

| Tracker | Blocked P1s | Evidence |
|---|---|---|
| `doc/08_tracking/todo/todo_db.sdn` + `doc/TODO.md` | 0 | Header states `Total: 312, Open: 312, Blocked: 0`; `P0/P1/P2 = 0`, all 312 are P3 |
| `doc/08_tracking/feature/feature_db.sdn` | 1 | `grep -oE '"[a-z_-]+", *"P[0-9]"'` → exactly one `"blocked", "P1"` (FR-GPU-BOARD-0002, line 9) |
| `doc/08_tracking/task/task_db.sdn` | 0 | Single row `TRACK-001`, status `in_progress` |
| `doc/03_plan/agent_tasks/**` | 3 rows, none P1 | `grep -rn 'BLOCKED'` → 3 hits, all lane notes |

The feature-DB row is included below as item 23 so nothing is silently dropped.

---

## 1. Baseline facts used by every verdict

These were measured on the audited tree and are cited as **B1/B2/B3** in the
rows.

- **B1 — the stale-seed condition STILL HOLDS.** `bin/simple` →
  `bin/release/x86_64-unknown-linux-gnu/simple` (mtime 2026-07-27 22:06). Running
  it emits `WARNING: this Rust-built Simple binary is a bootstrap seed only`,
  printed by `src/compiler_rust/driver/src/seed_warning.rs:20`. No full
  self-hosted CLI is deployed anywhere. `build/bootstrap/full/x86_64-unknown-linux-gnu/`
  is **empty** (dir mtime Jul 24 08:28). The only non-seed artifact,
  `build/aggfix/x86_64-unknown-linux-gnu/simple`, self-reports as
  `simple-bootstrap 1.0.0-beta` — a partial stage-2 product, not the CLI.
  **Consequence: "blocked on redeploy" is REAL-INTERNAL, not stale.**
- **B2 — the `readlink -f /proc/self/exe` fork-bomb/hang is GONE.**
  `bin/simple run <file>` returns promptly with an ordinary diagnostic.
  Any note claiming "the compiler hangs" from ≤2026-07-24 is stale on that point.
- **B3 — no startup segfault.** `bin/simple --version` exits 0 promptly.

### 1.1 The root blocker chain (governs most REAL-INTERNAL rows)

`doc/08_tracking/bug/stage4_focused_subbuild_star_import_unresolved_2026-07-27.md`
is the head. Line 15: *"bootstrap deploy did not occur; `bin/simple` still
resolves to..."*; line 171: *"remains the 2026-07-25 seed."*

That doc named two remaining stage-4 blockers (lines 150–165). **Both have
in-HEAD fixes that landed AFTER the doc was written**, and the doc was never
updated:

| Stated stage-4 blocker | Fix commit | In HEAD | Commits after bug doc |
|---|---|---|---|
| `me` unresolved (543 occurrences) | `8af2dc55596` fix(hir): alias `me` ↔ `self` when resolving a receiver identifier | YES | 26 |
| Module-key canonicalization | `584e74ece31` fix(driver): canonicalize module names across symlinked tier spellings | YES | 97 |
| " | `3eea09c6796` fix(driver): normalize symlink module spellings so package siblings match | YES | 92 |

Verified with `git merge-base --is-ancestor <sha> HEAD` and
`git rev-list --count bc6918126a7..<sha>`.

**The chain has since advanced to the link stage.** A newer bug,
`doc/08_tracking/bug/stage4_link_undefined_peer_symbols_2026-07-28.md`, records
compile 1584/1584 green and the build reaching final LINK, failing on two
undefined symbols. **This audit finds that doc already half-stale and its root
cause claim wrong on both counts:**

1. `resolved_theme_fingerprint` — the doc says `src/app/ui.web/html_css.spl:8`
   imports this stale name. **Already fixed and committed.** Line 8 at both
   `HEAD` and origin/main `5151659` reads
   `use nogc_sync_mut.ui.theme_package.{resolve_theme_alias, resolved_theme_css, theme_package_fingerprint}`
   — the correct name, called at `:26`. `git status --porcelain` on that file is
   clean, so this is committed, not a working-copy edit.
2. `run_test_api_server_with_inject` — the doc calls this a "genuine
   missing/renamed def". **It is not missing.** Defined at
   `src/app/ui.standalone/bootstrap.spl:36`, exported at
   `src/app/ui.standalone/__init__.spl:2`, imported at
   `src/app/office/sheets/access_server.spl:7`, called at `:23`.

The doc's heading "**Root (genuine missing/renamed defs, NOT compiler)**" is
therefore **wrong for both symbols**. The residual failure is a build-closure /
linked-set problem (the doc's own alternative hypothesis), or a stale `mod_251.o`.
No bootstrap has been re-run since Jul 24 (`build/*.log` bootstrap entries all
dated Jul 24).

**Highest-value action in this audit:** re-run
`sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy`.
Every stated blocker in front of it now has a landed fix or is provably a
non-issue in source. A successful deploy would clear the largest REAL-INTERNAL
cluster below in one move.

---

## 2. Audit rows

Classification key: **STALE** (blocker resolved, can restart today) ·
**REAL-EXTERNAL** (hardware/upstream/human decision) · **REAL-INTERNAL**
(blocked on named repo work) · **CIRCULAR** · **UNKNOWN** · **OBSOLETE**
(no longer describes anything real; recommend deletion, never silent removal).

### Tally

| Classification | Count |
|---|---|
| STALE — can restart today | **8** |
| REAL-INTERNAL | 11 |
| REAL-EXTERNAL | 3 |
| CIRCULAR | 1 |
| UNKNOWN | 0 |
| **Total** | **23** (22 bug files + 1 feature-DB row) |

Of the 8 STALE, **4 are recommended for deletion** as obsolete (rows 13, 15, 20,
and 3 once superseded). Deletion is *recommended*, not performed — per the repo
rule this audit removes nothing.

---

### STALE — blocker verified resolved; work can restart today

**3. `cranelift_seed_missing_sffi_externs_2026-07-16.md`**
- *Stated blocker:* "The deployed seed binary … exports only 68 of them"; first call `rt_cranelift_new_aot_module_triple` fails (`:20-22`, `:98-117`).
- *Verdict:* **STALE** — recommend supersede/close.
- *Evidence:* `nm` on `bin/release/x86_64-unknown-linux-gnu/simple` yields **80** distinct `rt_cranelift_*` symbols vs **75** declared in `src/lib/nogc_sync_mut/sffi/codegen.spl`; `comm -13 have want` is **empty** — nothing missing, including `rt_cranelift_new_aot_module_triple`. Independently re-run by the auditor. Live `native-build --backend cranelift` shows zero `unknown extern function: rt_cranelift_` and now fails downstream on an unrelated `error[E1002]: function 'source_file_coverage_identity' not found`.
- *Next action:* Re-run `scripts/check/check-native-seed-parity.shs` — `cranelift_seed_supported()` no longer downgrades, so all 9 `*_llvm_cranelift` cases execute for real for the first time. File the new `source_file_coverage_identity` failure as its own bug.

**5. `engine2d_cpu_offscreen_render_commands_first_frame_fault_2026-07-17.md`**
- *Stated blocker (current tail):* "Zero-fault-first-frame now blocked by the offscreen-surface-vs-192MB-bump-heap exhaustion" (`:271-275`). The original `cr2=0x0` framing is self-superseded at `:116`, `:208`.
- *Verdict:* **STALE**.
- *Evidence:* Both recommended remedies are implemented in `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`: reusable single-slot surface pool `_engine2d_embed_offscreen_acquire` at `:790` with state at `:785-788` (its comment at `:775-779` quotes this bug's exact `[PANIC] heap exhausted` failure), and the `baremetal_direct` gate at `:1202` consumed by `use_embedded_surface` at `:1203`. Landed in `f3ecb215ffb` / `0a97f5abd4e`.
- *Next action:* Re-boot `gui_entry_desktop.spl` via `scripts/check/check-simpleos-x86-64-wm-render-event-evidence.shs`; look for `first-frame-rendered` / `[WM] Glass desktop rendered!` plus a post-completion screendump. The doc's status header still reads "Open" with no entry past 2026-07-18.

**9. `interp_cross_module_struct_field_collision_2026-07-04.md`**
- *Stated blocker:* "Only the rebuild + `bin/release` DEPLOY (step 5, the hazardous shared-binary swap) … remain" (`:372`, `:376-378`, `:415-420`).
- *Verdict:* **STALE** — this is the one item whose awaited deploy has *already happened*.
- *Evidence:* The fix's marker constant `__simple_flatten_module_owner__=` (`src/compiler_rust/compiler/src/interpreter_state.rs:63`) is **present in the deployed binary** — `strings bin/release/x86_64-unknown-linux-gnu/simple | grep -c flatten_module_owner` → `1` (re-run by the auditor). Consumers at `interpreter_eval.rs:432,444` and `interpreter_call/mod.rs:148`. Note this item awaited the *seed* deploy, which is distinct from the still-pending self-hosted deploy of B1.
- *Next action:* Re-run the CARD 16 office/browser `default_style` repro and the release-build `simple_web_renderer_spec` against current `bin/simple`; if green, close and drop the "deferred coordinated deploy window" note. Re-check paired CARD 6 raw-mode extern from the same deploy.

**13. `native_class_array_field_mutation_segfault_2026-07-17.md`**
- *Stated blocker:* "the segfault DOES reproduce under `bin/simple run` … an extra per-CLASS header slot … Fixing that is out of scope here (it lives in `src/compiler_rust`, which is bootstrap-only)" (`:4`, `:117-121`).
- *Verdict:* **STALE / OBSOLETE — recommend deletion.**
- *Evidence:* The doc's own repro shapes were re-run on today's seed via `bin/simple run` (the only path it claims still crashes). Auditor's independent run — class with array field, method push ×3 plus index-assign — printed `len=3 v0=99 v2=9`, `EXIT=0`. No SIGSEGV, correct values. Current seed lowering derives offsets directly from `struct_fields`/`field_regs` with no phantom header slot (`src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs:116-137`).
- *Next action:* Re-run the `class_array_field_mutation` case in `scripts/check/check-native-seed-parity.shs`, then delete this doc — native-build was already correct and the seed-JIT half no longer reproduces.

**15. `simd_facade_encoding_utf8_missing_spl_2026-06-26.md`**
- *Stated blocker:* "Restore `src/lib/common/encoding/utf8.spl` … **Scope: encoding agent.**" plus fix `aes/cipher.spl` `import` → `use` (`:17-18`).
- *Verdict:* **STALE / OBSOLETE — recommend deletion.**
- *Evidence:* Both fixes are done, re-verified by the auditor. `src/lib/common/encoding/utf8.spl` exists (12,204 bytes) and defines exactly the two symbols the spec imports: `fn utf8_count_codepoints` at `:195`, `fn text_codepoint_len` at `:254`. `grep -c '^import ' src/lib/common/aes/cipher.spl` → **0**; it already uses `use std.common.aes.*`.
- *Next action:* Run `bin/simple test test/01_unit/lib/common/simd_dispatch_facade_spec.spl`; if green, delete this bug file.

**19. `theme_service_notification_transport_contract_2026-07-24.md`**
- *Stated blocker:* "Status: open, implementation blocked" (`:3`); "`ThemeService` does not own an `IpcOutputPort`, an injected send callback, a source port, or a … payload schema."
- *Verdict:* **STALE (self-inflicted mislabel)** — nothing external blocks this; it is ordinary unimplemented work recorded as "blocked".
- *Evidence:* The placeholder is real — `src/os/services/theme/theme_service.spl:59` defines `me _notify_all():` whose body is `pass_dn` at `:64`. But the API it claims to be missing **already exists**: `struct IpcOutputPort` at `src/os/kernel/ipc/ports.spl:17` with field `send_fn: fn(IpcMessage) -> i64` at `:25`. Nothing prevented the author from wiring it.
- *Next action:* Give `ThemeService` an `IpcOutputPort` (or injected `send_fn`), define the theme-change method/payload schema, and replace the `pass_dn` at `:64`. Then re-label: this is a TODO, not a blocker.

**20. `wasm_cli_emit_no_artifact_2026-05-30.md`**
- *Stated blocker:* header already reads "likely-fixed (triaged 2026-06-11 …)"; the tracked claim was that the WASM CLI emits no artifact.
- *Verdict:* **STALE / OBSOLETE — recommend deletion.**
- *Evidence:* Auditor compiled a trivial program end-to-end: `bin/simple compile --target=wasm32-unknown-unknown /tmp/w2.spl -o /tmp/w2.wasm` → `Compiled ... -> /tmp/w2.wasm`, exit 0, **548-byte** artifact with valid WASM magic `0061 736d 0100 0000`. An artifact is emitted.
- *Next action:* Delete the file, or convert to a regression spec asserting a non-empty `.wasm` with correct magic.

**22. `wm_showcase_no_headless_lane_2026-07-25.md`**
- *Stated blocker:* "CONSTRAINT IDENTIFIED - Evidence collection blocked on shared hardware" (`:4`) — i.e. no headless lane exists.
- *Verdict:* **STALE**.
- *Evidence:* A headless capture lane now exists and Xvfb is installed. `examples/06_io/ui/wm_widget_showcase_gui.spl:467` reads `# Headless host-WM capture lane (SIMPLE_WM_HEADLESS_CAPTURE=1)`, with 5 total `SIMPLE_WM_HEADLESS_CAPTURE*` references including bridge/frame timeouts at `:545`, `:561`. `which Xvfb` → `/usr/bin/Xvfb`. Both re-checked by the auditor.
- *Next action:* Run the showcase under `SIMPLE_WM_HEADLESS_CAPTURE=1` on Xvfb and attach the captured frames as the evidence this item was waiting for. No shared-hardware slot is needed.

---

### REAL-INTERNAL — blocked on named repo work

Rows 2, 6, 8, 12, 14, 18, 21 all terminate on the **same single dependency**:
the stage-4 bootstrap producing and deploying a self-hosted `bin/simple` (B1,
§1.1). They will clear together.

**2. `browser_engine_viewport_height_margin_2026-07-11.md`** — *Stated:* "the focused scenario has not been executed because the tracked target compiler failure exhausted its three allowed repair cycles" (`:45-47`). *Verdict:* REAL-INTERNAL on B1. *Evidence:* the fix IS landed — `resolve_vertical_margin_px` at `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl:468`, called `:546,:561,:1318`; scenario exists at `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl:924` (`margin-top:40vh`). Running it gave exit 255 / `Process timed out` after ~8 min with **no compiler error** across 5252 log lines — so the *named* compiler failure is stale; the executable gap is the seed-vs-self-hosted issue.

**4. `c_runtime_exclusion_analysis_2026-05-18.md`** — *Stated:* Group B "removal requires … a pure-Simple replacement exporting the same symbol name" (`:233-236`). *Verdict:* REAL-INTERNAL (ordinary work, nothing external) **and the audit data is OBSOLETE**. *Evidence:* all 12 Group B/C files still on disk, but `:65` claims "23 top-level `src/runtime/*.c` files remain" while the actual count today is **35**; the proposed `--bootstrap-exclude-legacy-runtime` flag (`:238-240`) has **zero** hits in `src/` or `scripts/` — never wired. *Unblocked subset now:* delete the two already-cleared stale duplicates `hosted_cocoa.c` / `hosted_win32.c` (`:113-114`), and re-run the audit — it is 2 months stale and 12 files behind.

**6. `f64_self_hosted_call_result_codegen_2026-06-21.md`** — *Stated:* "Stage 3 self-host fails (LIM-010) … freshly-bootstrapped stage4 **coredumps on trivial programs** … so there is no working build→run loop" (`:38-42`). *Verdict:* REAL-INTERNAL on B1. **Its regression gate is FALSE-GREEN — see §3.** *Evidence:* the "stage4 coredumps on trivial programs" claim is itself stale (stage4 has since advanced to the link stage, §1.1), but no deploy has occurred so the loop is still absent.

**8. `if_val_some_constructor_pattern_parser_regression_2026-07-02.md`** — *Stated:* "deployed binary pending bootstrap — stage2 blocked by unrelated `rt_cranelift_new_aot_module` extern error" (`:2`). *Verdict:* REAL-INTERNAL on B1; **the named sub-blocker is STALE**. *Evidence:* auditor confirmed `rt_cranelift_new_aot_module` is now declared at `src/lib/nogc_sync_mut/sffi/codegen.spl:14` (and `_triple` at `:15`) and registered in the seed extern table at `src/compiler_rust/compiler/src/elf_utils.rs:725`. Source fix present at `src/compiler/10.frontend/core/parser_stmts.spl:686-689` and `:912-919`.

**11. `macos_vulkan_2d_vector_font_empty_batch_native_fault_2026-07-26.md`** — *Stated:* "open, live evidence blocked" (`:3`); "Vulkan live evidence remains blocked" (`:345`). *Verdict:* REAL-INTERNAL — blocked on the native pixel-bearing-return lowering defect in `sfnt_glyf`, **not** on macOS. *Evidence:* the active failure (cycles 19-21, `:390-406`) is `fail-glyph-bitmap-pixels`, reproduced **locally on this Linux host** with the pure-Simple Stage3 diagnostic compiler (185 modules, zero compile failures); blob/outline/metrics proven sound. Actively worked in `ad5aa52493d` and `25a2b59d748` (both 2026-07-27). Only the final macOS Vulkan *attestation* needs a Mac (row 10). *Also fixable now:* the `fn`-reading-`self` nil-receiver trap on `Engine2D.font_execution_attempts()/font_execution_target()` (`:22-25`).

**12. `native_build_worker_zombie_parent_hang_2026-07-03.md`** — the only item in the population carrying an explicit **P1**. *Stated:* "Fresh self-hosted execution therefore remains blocked, and the known-stale binary is not accepted as replacement evidence" (`:126-128`). *Verdict:* REAL-INTERNAL on B1. *Evidence:* `build/bootstrap/full/x86_64-unknown-linux-gnu/` is **empty** (auditor-confirmed; dir mtime Jul 24 08:28) — the target of the item's own stage-4 command. The 2026-07-23 parent-death fix itself HAS landed: `rt_process_spawn_guarded` at `src/runtime/runtime_legacy_core.c:598`, `src/runtime/runtime_native.c:6322`, `src/app/io/process_ops.spl:17`, plus `scripts/check/check-process-parent-death.shs`.

**14. `native_selfhosted_run_segfault_startup_normalize_2026-07-24.md`** — *Stated:* "the redeploy that would let the proving gate run is gated on the parse-memory-balloon fix (interning)" (`:139-142`). *Verdict:* REAL-INTERNAL on B1 / the redeploy, **not** on this bug's own fix. *Evidence:* `git cat-file -t 00bfd7cfb0e` → `commit`, and `git merge-base --is-ancestor 00bfd7cfb0e HEAD` → YES, so the guard IS in history, with its test at `src/compiler_rust/compiler/tests/compile_and_run.rs:280`. `rt_string_free` primitives landed (`d55fe0c67d6`, `9b97fa0c22b`, `3fefd710dd4`). Per B1 no self-hosted binary exists, so the proving gate still cannot run. The user-facing symptom is currently absent only because `bin/simple` is the seed.

**16. `simpleos_rv64_wm_live_framebuffer_gate_2026-06-30.md`** — *Stated:* "`vfs_boot_init_virtio_fat32()` reaches the ARM-only `rt_arm_virtio_blk_*` ABI … with no architecture-neutral `BlockDevice`/FAT32 sector-byte interface" (`:33-45`), plus "no RV64 production caller" for VirtIO input (`:46-50`). *Verdict:* REAL-INTERNAL — blocked on the missing shared VirtIO-BLK sector-byte adapter. The input half has **closed**. *Evidence:* input gap closed — `src/os/kernel/arch/riscv64/virtio_input.spl` exists and is referenced by `examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl`. Block gap **holds and is worse than documented**: auditor confirmed the 20-extern surface at `src/os/drivers/virtio/_VirtioBlk/driver_class.spl` (20 `rt_arm_virtio_blk` references) has **zero** definitions anywhere — `grep -rl 'rt_arm_virtio_blk' src/ --include=*.c --include=*.h` is empty. So `vfs_boot_init_virtio_fat32` (`src/os/services/vfs/vfs_boot_init.spl:1288`) resolves to nothing **on any arch** — a live WEAK auto-stub hazard, see §3. The doc's cited "TODO 548 / TODO 567" are not in `todo_db.sdn` (stale refs).

**17. `stage4_cranelift_direct_enum_text_cross_function_2026-07-24.md`** — *Stated:* "Declaration-driven registration … is **blocked** by a codegen defect": nested enum-typed HIR field `v.kind` mis-decodes in native-compiled `module_lowering` (`:48-49`, `:51-74`). *Verdict:* REAL-INTERNAL on the native-codegen nested-aggregate mis-decode family **and** on B1. *Evidence:* neither candidate fix landed — `enum_tuple_text_slots` has only 4 references in `src/compiler`: declared `50.mir/mir_lowering_types.spl:174`, initialized `_MirLowering/module_lowering.spl:135`, read `_MirLoweringExpr/switch_operators_calls.spl:1372`, written **only** at construction `:1699`. Registration is still order-dependent exactly as described. Family still live per `doc/07_guide/language/dict_native_pitfalls.md:1-8`. Direct-lane re-verification not achievable: `native-build --backend cranelift` on the minimal probe exceeded 600s under the seed and was killed. The probe prints correctly under `bin/simple run`, but that is the seed JIT, **not** the affected lane — not counter-evidence.

**18. `stage4_selfhost_log_modes_lexer_state_corruption_2026-07-24.md`** — *Stated:* "open; exact-current full CLI blocked" (`:3`); "blocked until a test-capable exact-current CLI can be produced" (`:67`). *Verdict:* REAL-INTERNAL on B1. *Evidence:* the item's own exit condition is literally a working exact-current full CLI, which B1 shows does not exist. Auditor note: the file has moved to `src/lib/nogc_async_mut/cli/log_modes.spl` (the doc's `src/compiler/00.common/log_modes.spl` path no longer exists — path reference is stale); `bin/simple check` on it exceeded 120s under the seed, so no seed-side conclusion is available either way. First observed on macOS arm64.

**21. `webgui_font_path_seed_verification_2026-07-20.md`** — *Stated:* "Open (verification blocked by pre-existing seed defects; no new product defect found in the font path itself)" (`:3-4`); "the only deployed `bin/simple` is the **Rust seed** … the pure-Simple self-hosted binary is not deployed." *Verdict:* REAL-INTERNAL on B1. *Evidence:* the doc's own tooling-reality statement is **still exactly true today** — B1 re-confirms `bin/simple` emits the seed warning and no self-hosted binary is deployed. The item explicitly found no product defect in the font path, so it is purely a verification-tooling block.

---

### REAL-EXTERNAL — hardware, upstream, or a human decision

**7. `gui_web_2d_vulkan_pairwise_aggregate_2026-06-22.md`** — *Stated:* "pass for pairwise pixels; browser/RenderDoc completion still blocked" (`:4`); `browser_backing_reason=electron-vulkan-disabled_off` (`:33`). *Verdict:* REAL-EXTERNAL for the Electron half; **the RenderDoc half is actionable now**. *Evidence:* `:152-165` documents three exhausted Electron paths (flags, `appendSwitch`, direct launcher) all yielding `hardwareSupportsVulkan=false`, needing a different Electron/GPU host. Separately `build/gui-web-2d-vulkan-env/evidence.env` (Jul 26 11:22) shows `renderdoc_status=unavailable`, `reason=missing-renderdoccmd-in-search-paths`; `which renderdoccmd` empty. **That run produced no `pixel_comparison_*` / `browser_backing_*` rows at all** — it aborted at RenderDoc setup, so the in-file pass rows are stale-by-run. *Partially actionable:* install RenderDoc and re-run `scripts/setup/setup-gui-web-2d-vulkan-env.shs --run`.

**10. `macos_full_cli_gui_admission_process_proof_2026-07-27.md`** — *Stated:* "The tracked policy remains `status=unavailable` with unassigned signing and toolchain identity and therefore exits 125" (`:40-43`); remedy "Provision an approved macOS signing team and Endpoint Security entitlement" (`:47`). *Verdict:* REAL-EXTERNAL. *Evidence:* requires an Apple Developer team plus an Apple-granted Endpoint Security entitlement — a vendor/human decision, not repo work. No Mac in `doc/08_tracking/hardware/` (contents: `golden_vhdl_manifest_2026-07-26.txt`, `hardware_manifest.sdn`, `riscv64_fpga_inventory_2026-05-19.md`). GitHub `macos-latest` / `macos-15-intel` runners exist (`.github/workflows/rust-bootstrap-multiplatform.yml:159,165`) but cannot supply an ES entitlement or signing identity.

**23. `FR-GPU-BOARD-0002` — feature-DB row (`doc/08_tracking/feature/feature_db.sdn:9`)** — the **only** row anywhere carrying an explicit `"blocked", "P1"`. Title: "Add VisionFive 2 BXE native GPU adapter". *Stated blocker:* "Retain the BXE-4-32 row as blocked while current upstream Mesa lists it unsupported." *Verdict:* REAL-EXTERNAL. *Evidence:* the board is not available — `grep -ci 'visionfive\|jh7110' doc/08_tracking/hardware/hardware_manifest.sdn` → **0**; the manifest's only board entry is `abx00162` (Arduino UNO Q). VisionFive 2 appears only in planning/design prose (`doc/05_design/simpleos_qemu_host_gpu_2d.md`, `doc/07_guide/platform/simpleos/simpleos_baremetal_board_support.md`), never as owned hardware. The Mesa-support condition is upstream and not checkable in-repo. Correctly classified as blocked; keep.

---

### CIRCULAR

**1. `bootstrap_low_memory_positional_bridge_circularity_2026-07-26.md`** — *Stated:* "No currently available **eligible** pure-built macOS/arm64 binary has both capabilities needed by the live gate" (`:26-27`); unblocking needs a restored runtime capsule `02775039b2…` **and** "high-capability approval" (`:239-250`). *Verdict:* **CIRCULAR**, with a REAL-EXTERNAL half. *Evidence:* Prereq 2 (`:248-250`) is an explicit human-approval gate — not resolvable by repo work. Prereq 1 needs an artifact the doc itself records as absent (`:220-221`). Both binaries are macOS/arm64 under `/Users/ormastes/simple`, unreachable from this Linux checkout. The item is self-described as circular (`:24` "## Exact circularity", `:54` "This is a real bootstrap circularity"). **Nothing will unblock this without a human decision.** The doc reserves "exactly one bounded micro cycle" (`:235`) that must not be spent casually.
- *Note:* no CIRCULAR **pairs** exist in this population. Cross-referencing every one of the 22 files against every other by filename produced **zero** mutual references, so there is no A↔B deadlock; this row is a single self-contained cycle against an external approval.

---

## 3. Cross-cutting defects found during the audit

These were not in scope but were found while verifying, and each is a live
correctness risk. None is fixed by this audit.

**C1 — `check-f64-call-abi.shs` is FALSE-GREEN.** The script prints
`jit: 21.5 PASS — self-hosted f64 call-result codegen is fixed` and exits 0
(auditor re-ran it). This is invalid. Its own header at `:12` states *"This
script targets the deployed self-hosted `bin/simple`"*, but per B1 `bin/simple`
is the Rust seed, which was already fixed by `07d87555f0e`. The gate is
measuring the seed's Rust cranelift codegen, **not**
`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`. It therefore
asserts a self-hosted codegen bug is fixed on a code path that was never
executed, and it makes row 6's fix-checklist step 4 (`:62`) untrustworthy.
*Recommended fix:* add a seed classifier — the binary self-identifies with
`bootstrap seed only` — and report `PENDING` instead of `PASS` until a genuinely
self-hosted `bin/simple` exists.

**C2 — `rt_arm_virtio_blk_*` is 20 declared externs with zero definitions.**
Confirmed by the auditor: `src/os/drivers/virtio/_VirtioBlk/driver_class.spl`
carries 20 `rt_arm_virtio_blk` references, and
`grep -rl 'rt_arm_virtio_blk' src/ --include=*.c --include=*.h` returns
**nothing**. This is precisely the WEAK nil-returning `rt_*` auto-stub hazard
class: `vfs_boot_init_virtio_fat32` (`src/os/services/vfs/vfs_boot_init.spl:1288`)
silently resolves to nothing **on every architecture**, not just RV64. Worth its
own bug; row 16 understates it as an RV64-only gap.

> **RETRACTED 2026-07-28 — both factual claims above are wrong.** See
> `doc/08_tracking/bug/rt_arm_virtio_blk_prefix_allowlist_defeats_fabrication_guard_2026-07-28.md`.
> (a) *Method error:* the cited grep was scoped to `src/`, but the definitions
> live at `examples/09_embedded/simple_os/arch/{arm64,arm32}/boot/baremetal_stubs.c`
> — **14 real strong definitions each**. The true population is **12 declared
> externs** (`driver_class.spl:118-132`); "20" counted references, not
> declarations. (b) *"Every architecture" is false:* `vfs_boot_init_virtio_fat32`
> has exactly one production caller,
> `examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl:153`, and
> tests assert the RV64/x86_64 guests do not call it. The single arch that
> reaches this code is the one that implements it for real. Row 16's RV64
> framing was closer to correct than this item's generalization.
>
> A **real but different** defect was found in its place:
> `simpleos_rt_symbol_is_optional_backend`
> (`src/compiler/70.backend/backend/llvm_native_link.spl:1752`) allowlists
> `rt_arm_virtio_` by **prefix**, sweeping a storage read path into the
> "nil means backend unavailable" bucket — the exact mistake that function's own
> docstring refuses to make for `rt_simd_`. Six `rt_arm_virtio_blk_*` symbols are
> confirmed `W` (weak) in a built guest ELF. Severity is bounded: the surface is
> read-only, so the failure mode is silently wrong reads / FAT32 mis-parse, not
> write-drop or on-media data loss.

**C3 — `stage4_link_undefined_peer_symbols_2026-07-28.md` misattributes its own
root cause.** Filed today, its heading claims "Root (genuine missing/renamed
defs, NOT compiler)". Both named symbols are refuted in §1.1: symbol 1's rename
is already fixed and committed at HEAD *and* origin/main, and symbol 2 is
defined, exported, and imported correctly. The residual failure is a
build-closure / linked-set problem or a stale `mod_251.o`. Because this doc is
the head of the redeploy chain, its wrong root cause is currently misdirecting
the single highest-leverage lane in the repo.

**C4 — status vocabulary is unnormalized, which is why nobody could count these.**
`doc/08_tracking/bug/*.md` status lines use at least 20 spellings
(`open` 58, `Resolved` 33, `RESOLVED` 28, `FIXED` 26, `Open` 21, `OPEN` 21,
`fixed` 20, `closed` 18, `Fixed` 17, `resolved` 12, `likely-fixed` 9,
`SOURCE-FIXED` 6, `**RESOLVED` 6, `Closed` 6, `source` 5, `STALE` 4, …), and
blocked-ness is expressed in free prose across four different field names
(`Status`, `Verdict`, `State`, `Classification`). Only **one** file in 1,461 has
a machine-readable `Status: BLOCKED`. That is why the "22 P1 blocked" figure
could be neither confirmed nor traced to a source. *Recommended fix:* a
controlled status vocabulary plus a required `priority:` field, enforced by a
`scripts/check/` gate.

**C5 — the population carries almost no priority data.** 21 of 22 files have no
`P0`–`P3` token at all (§0). Any future statement of the form "N P1 items are
blocked" is unsupportable until C4 is fixed.

---

## 4. Recommended order of work

1. **Re-run the stage-4 bootstrap deploy** (§1.1). Every stated blocker ahead of
   it now has a landed fix or is provably a non-issue in source, and no bootstrap
   has run since Jul 24. Success clears 7 REAL-INTERNAL rows at once.
2. **Fix C1** before trusting any self-hosted codegen gate.
3. **Work the 8 STALE rows** — all are restartable today with no new dependency.
4. **Delete the 4 obsolete docs** (rows 13, 15, 20, and 3 once superseded) —
   explicitly, with the evidence above recorded, never by silent omission.
5. **File C2 and C3** as their own bugs.

## 5. Method and honesty notes

- Every verdict cites a file:line, a command result, or a sha. No verdict rests
  on "looks resolved".
- Greps used for counting were anchored and spot-checked, per
  `doc/07_guide/infra/debugging/measurement_traps.md`.
- All STALE verdicts and both cross-cutting binary claims (C1, C2) were
  re-executed independently by the auditor rather than taken on report.
- **Nothing was deleted, and no blocked work was started.** This is an audit;
  the deliverable is a trustworthy list.
- **Nothing was marked unblocked without proof.** Where proof was unobtainable
  the row says so — e.g. row 17, where the affected native lane could not be
  re-run because `native-build --backend cranelift` exceeded 600s under the seed,
  and the seed-JIT result is explicitly rejected as counter-evidence.
- Zero rows are UNKNOWN.
