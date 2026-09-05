# WM + Render + SimpleOS-Runnable + Harden-Plan Mission Status

Date: 2026-08-08
Scope: standing mission "complete wm and render lane, simple os runnable, and harden plan"
Sourced entirely from `origin/main` history (`git log --oneline origin/main`, `git show <sha>`). Every sha below was verified with `git cat-file -t <sha>` = `commit` before inclusion.

## Top-line verdicts

| Lane | Verdict |
|---|---|
| 1. Render-perf (T7/T16/T17) | **COMPLETE** |
| 2. 2D-Vulkan coverage gate | **SUBSTANTIALLY COMPLETE** (gate green; decision coverage below target; no Vulkan backend on SimpleOS) |
| 3. WM lane | **SUBSTANTIALLY COMPLETE** (specs + defect fix landed; coverage baseline recorded, not at target) |
| 4. Web-CSS lane | **COMPLETE** (grid/text suites green modulo one known flake) |
| 5. Coverage tooling | **IN PROGRESS** (RC1 fixed+verified; RC2 fixed, awaiting rebuild/deploy; collector blind spots cap several targets) |
| 6. SimpleOS-runnable (QEMU boot) | **IN PROGRESS — blocked** (kernel builds to freestanding link; QEMU boot not yet achieved) |
| 7. Bootstrap (Stage 2 / Stage 3) | **PARTIAL** (Stage 2 fixed and verified; Stage 3 monomorphize SIGSEGV OPEN) |

---

## 1. Render-perf lane — COMPLETE

- **T7 — JIT named-fn-as-value guard**: `45e0e8d68b7` "fix(compiler): JIT guard for named-fn-as-value silent miscompile (T7)". Closes the silent-miscompile hazard for named-function references passed as values under JIT.
  - Follow-up still open: extern-fn-as-value still miscompiles under JIT (tracked as `jit_extern_fn_as_value_still_miscompiles`, noted explicitly in `c7a0746702f`'s commit message: "note extern-fn JIT gap"). This is a narrower residual, not a T7 regression.
- **T16 — blend-span kernels**: three-part landing —
  - `ccf1b9f48b5` "fix(runtime): add missing rt_engine2d_simd_blend_span_u32/_const_span_u32 native symbols" (Rust runtime symbols)
  - `a399483dea7` "fix(gpu): wire span-bridge intrinsics into MIR lowering and LLVM decls"
  - `796d8484b7c` "fix(compiler): register blend-span SIMD kernels in self-hosted MIR/LLVM" (self-hosted registration)
- **T17 — examples-timeout**: `0027a8b6715` "docs(bug): T17 -- re-verify wm/web showcase child-frame timeout on redeployed binary".

Status: all three render-perf work items (T7, T16, T17) have landed commits on `origin/main`; T7's sibling extern-fn defect remains open and tracked separately.

## 2. 2D-Vulkan coverage lane — SUBSTANTIALLY COMPLETE

- Gate `check-render2d-coverage.shs` now passes its mechanical prerequisites 5/5, landed across two commits:
  - `2effdbde400` "fix(check): render2d coverage gate — real mechanical probes for prereqs 1/2/3/5"
  - `c7a0746702f` "fix(gate,jit,docs): close render2d gate fail-open, note extern-fn JIT gap, fix span-bridge/coverage report nits" (closes a fail-open hole in the gate itself)
- Decision coverage:
  - C2 (kernel_registry residual-arm decisions): `caa21641089` "test(engine2d): close kernel_registry residual-arm decisions — C2 31/68 -> 49/68" → 72.1%.
  - C3 (os/compositor decisions): progressed `827fabedab8` "test(os/compositor): C3 decision-coverage closure — 207 baseline 17.9%→27.5%", then re-measured after the coverage `<entry>` attribution fix in `2a3695e6c46` "docs(ui): re-measure C3 compositor coverage after <entry> attribution fix".
- **Important scope note, stated honestly**: there is **no Vulkan backend for SimpleOS baremetal** — the 2D renderer on SimpleOS is a CPU rasterizer only. "2D-Vulkan coverage" in this mission refers to the host-side/engine2d coverage gate and decision-coverage numbers, not a baremetal Vulkan path.
- Verdict: the gate is green and mechanically real (fail-open closed), but C2/C3 decision-coverage numbers (72.1% / 27.5%) sit below typical target bands — hence substantially complete, not complete.

## 3. WM lane — SUBSTANTIALLY COMPLETE

- System specs for window lifecycle, focus/z-order, damage/present-skip, and input-routing landed and closed out with a baseline: `18a88bdb3fb` "docs(wm): WM system-spec implementation coverage baseline + closure".
- Input-routing passthrough defect fixed: `49e7a5f6c27` "fix(wm): pointer-events passthrough for overlap hit-testing + pointer_move field-drop".
- Verdict: specs exist, the identified defect is fixed, and a coverage baseline is recorded — but the baseline commit is explicitly a "baseline," not a statement that WM impl coverage hits a target threshold, so this is substantially complete rather than fully complete.

## 4. Web-CSS lane — COMPLETE

- Ellipsis: `34095840bbd` "fix(browser_engine): Draw IR text-overflow:ellipsis truncation; triage grid/text RED examples".
- Grid fr-tracks: `3e56ef9cb63` "feat(browser-engine): resolve CSS Grid `fr` track units".
- Grid-template-areas + auto-flow:column: `eee74d337b4` "feat(browser_engine): CSS Grid grid-template-areas and grid-auto-flow:column".
- Overflow-wrap: `6fa4098dfb4` "fix(web-css): thread layout's precomputed wrap ranges into Draw IR text emission".
- Result (per task brief, consistent with the commit sequence): web_css_grid 6/6; web_css_text_layout 5–6/6 with one known line-height flake — i.e., functionally complete with one documented non-blocking flake.

## 5. Coverage tooling lane — IN PROGRESS

- spl-coverage CLI + decision probes + rollup exist and are the instrument used by lanes 2/3 above.
- `<entry>` attribution RC1 (impl-methods mis-filed under `<entry>`): fixed in `b6a43042cda` "fix(coverage): tag impl-block method owners so decision/line rows stop landing on <entry>"; re-measured result baremetal_core 6%→86%.
- RC2 (entry-script functions mis-filed under `<entry>`): fixed in `40fa02ee5a4` "fix(compiler): coverage `<entry>` fallback for entry-script functions (RC2)" — **awaiting a stage2 rebuild/redeploy** before the fix is live in the deployed measurement path (consistent with the deployed-binary-is-stale pattern recorded elsewhere in this repo's history).
- Collector blind spots: the collector cannot currently attribute hits to signature lines, tail-expression lines, or `elif` lines, which structurally caps how high some line-coverage numbers (e.g., 90% targets) can go until the collector itself is extended — this is a documented, not silently-accepted, limitation.
- Browser-engine closures cited in this mission: layout 98%, paint_primitives 85.1% (target met), core 81%, paint_layout 55.5% — paint_layout and core sit below common targets and are explicitly capped by the collector gap above, not by missing test-writing effort.

## 6. SimpleOS-runnable lane — IN PROGRESS, blocked (the hardest lane)

- `resolved_backend` inference fix unblocked the kernel build: `521ed055b76` "fix(web-render): declare resolved_backend field, unblock SimpleOS kernel build".
- Freestanding-symbol gap (originally 13 missing symbols) cleared across three commits:
  - `136f0769e37` "fix(os): implement 7 of 13 freestanding fabricated-stub symbols for SimpleOS WM kernel"
  - `0d83c56140c` "fix(os): device-absent CUDA/Metal bodies unblock SimpleOS freestanding link" (6 GPU device-absent bodies)
  - `66959c6b7ca` "feat(runtime): rt_file_is_char_device — drop last shell-out in virtio-gpu probe" (host + baremetal, closes the final symbol)
- The earlier Engine2D-struct-field root cause (traced from a mis-attributed "mod.spl" theory to the correct "engine.spl" location per `6246f3104db` "docs(bug): correct engine2d GPU-backend root cause from mod.spl to engine.spl") is corrected and reflected in the fixes above.
- **Current state, stated plainly**: the kernel now builds through to a freestanding link. **QEMU boot has NOT yet been achieved this session.** The `be775aa04fd` "docs(os): SimpleOS 2D render QEMU evidence — blocked at native build (HIR gap)" record predates the freestanding-link fixes above and needs to be re-run now that `rt_file_is_char_device` (`66959c6b7ca`) is in the tree — that requires a stage2 rebuild carrying this symbol, followed by a fresh QEMU attempt to discover the next blocker (if any). No commit in this range claims a successful QEMU boot or an on-screen render.
- The PML4-reads-zero-after-init blocker (tracked in `doc/08_tracking/bug/simpleos_vmm_kernel_pml4_phys_reads_zero_after_init_2026-08-06.md`) is confirmed **fixed and orthogonal** to the current freestanding-link blocker — it does not need to be revisited to make progress here, but it is a separate defect record, not folded into this lane's remaining work.
- Per the board-runnable rule (`.claude/rules/board-runnable.md`): this lane is currently QEMU-and-below (not yet booting in QEMU at all), so there is no board-runnable claim to make yet either. This must not be silently scoped down to "QEMU-only is fine" — it is stated here as an explicit open gap.

## 7. Bootstrap — PARTIAL

- Stage 2 was broken by a cross-session `Mailbox` → `PriorityMailbox` rename that left dangling references and resurrected deleted re-exports; fixed in `e7df6e011e5` "fix(async): complete Mailbox -> PriorityMailbox rename, unblock Stage 2", verified `STAGE2_EXIT=0`.
- Stage 3 monomorphize SIGSEGV (method=`len`) remains **OPEN** — no backtrace has been captured for it in this range; it is not addressed by any commit above.

## 8. Defects fixed (with shas)

| Defect | Sha |
|---|---|
| SIMD env default (`simd_config_mode()` treats nil env as unset) | `1365d5a6ec6` |
| Virtio-GPU probe: char-device check instead of mere existence | `c2fc508a82d` |
| Virtio-GPU probe: shell-injection hole closed | `6a53089f6fc` |
| Virtio-GPU probe: shell-out replaced with `rt_file_is_char_device` | `66959c6b7ca` |
| `paint_rect` clips negative/overflowing x span instead of bleeding rows | `d129996a8a3` |
| Span-bridge compiler defect (MIR lowering + LLVM decls for span-bridge intrinsics) | `a399483dea7` |
| JIT named-fn-as-value silent miscompile (T7) | `45e0e8d68b7` |

## 9. Regression sweep

- `bf574c7f5df` "docs(testing): session regression sweep vs deployed bin/simple — 11 clean, 0 new regressions" — 11 suites run against the deployed binary, 0 new regressions introduced by this mission's changes.

## 10. Open items (honest accounting)

- **Stage-3 monomorphize SIGSEGV** (method=`len`) — open, no backtrace captured.
- **SimpleOS QEMU boot** — not yet achieved. Needs: (a) stage2 rebuild carrying `rt_file_is_char_device` (`66959c6b7ca`), (b) a fresh QEMU attempt against the now-freestanding-linkable kernel to discover whatever the next blocker is. Do not report QEMU 2D render as working — it is not, as of this report.
- **JIT extern-fn-as-value miscompile** — open, sibling of the now-fixed named-fn-as-value defect (T7); noted in `c7a0746702f`.
- **Coverage RC2** (`40fa02ee5a4`) — fixed in source, awaiting stage2 rebuild + redeploy before the deployed measurement path reflects it.
- **core.spl / paint_layout.spl line coverage** (81% / 55.5%) — below common line-coverage targets; capped by documented collector blind spots (signature lines, tail-expression lines, `elif` lines are not attributable), not by unwritten tests. Raising these targets requires extending the collector first.
- **C2/C3 decision coverage** (72.1% / 27.5%) — real, gate-verified numbers, but below typical target bands; further closure work remains.
- **WM impl coverage baseline** — recorded (`18a88bdb3fb`) but is a baseline snapshot, not a claim of target attainment.

---

*This report is sourced from `origin/main` only; the local working copy was not used as a source of fact per repo policy on shared-WC staleness. All commit shas were independently verified with `git cat-file -t` before citation.*
