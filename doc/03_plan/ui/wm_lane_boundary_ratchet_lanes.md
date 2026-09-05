# Task #61 — WM Lane-Boundary Ratchet Burn-Down (219 → 0, in tranches)

Status: plan (dispatch document). Gate infrastructure already landed
(`7c337bd538b`): WML001/WML002 lints in
`src/compiler/90.tools/lint/_LintMain/wm_lane_boundary_lints.spl`, checker
`src/app/check/wm_lane_boundary_check.spl`, wrapper
`scripts/check/check-wm-lane-boundary.shs` (fail-closed: PASS/FAIL/ERROR as
the LAST stdout line; exit 2 = nothing checked), baseline
`doc/08_tracking/wm_lane_boundary_baseline.txt` (219 entries + 3 header
lines; may only SHRINK). Scope dirs: `wm_lane_scope_dirs()` at
`wm_lane_boundary_lints.spl:51` (13 dirs). Ground rules §1–§7 of
`doc/03_plan/runtime/native_binding/dlopen_conversion_lanes.md` apply to every
lane here (exclusive owns, verdict-line discipline, sabotage, engines stated,
commit-per-lane).

## Invariants for every tranche

- **Entry count**, not line count, is the ratchet number:
  `/usr/bin/grep -c ":WML" doc/08_tracking/wm_lane_boundary_baseline.txt`
  (219 today). Each tranche states its exact expected post-count.
- **Behavior preservation oracle:** BEFORE editing, run the specs under
  `test/` that mirror every owned file (mirror rule,
  `.claude/rules/structure.md`) and record their
  `SPEC FILE VERDICT` lines to a file. AFTER editing, re-run identically:
  every executed count must EQUAL its before-value and `failed=0 dropped=0`.
  Comparing counts (not just failures) is mandatory — a module-load failure
  drops whole describes at exit 0. If a touched file has no mirroring spec,
  say so in the report; do not invent a floor.
- Engine: whatever engine the mirroring specs already run under (default
  runner). The lint checker itself is engine-independent (source scan).

## Safe baseline-update procedure (the only permitted way)

1. Make the code change. Run `sh scripts/check/check-wm-lane-boundary.shs`
   from the repo root — the last stdout line must be `PASS` (zero NEW
   violations). `FAIL` or `ERROR` = stop; never proceed past an ERROR
   (exit 2 means nothing was checked, not "clean").
2. Regenerate: `sh scripts/check/check-wm-lane-boundary.shs --write-baseline`.
3. Verify the shrink: `git diff doc/08_tracking/wm_lane_boundary_baseline.txt`
   must show ONLY removed entry lines (line-number drift within an unchanged
   file is acceptable only for files the tranche edited); entry count equals
   the tranche's stated expected number exactly.
4. Commit the baseline IN THE SAME COMMIT as the code change (a baseline-only
   commit invites a parallel lane to regenerate against different code).
5. After any rebase and before push, re-run step 1 — parallel sessions
   force-push `main` continuously and the baseline is a shared file; on
   conflict, regenerate (step 2) on the rebased tree rather than hand-merging.

## Mandatory sabotage per tranche (same three, run all)

1. Re-add ONE removed violating import to one owned file → checker last line
   `FAIL` listing `NEW VIOLATION <that path>`. Revert.
2. Temporarily move the baseline file aside → checker must report `ERROR`
   (exit 2), NOT pass. Restore.
3. One behavior spec from the preservation oracle, sabotaged in its subject
   (tranche-specific, listed below) → its verdict goes `failed>=1`. Revert.

## Tranche graph

```
Now:       W1 (lib timers, 22ish edges)    W3 (small remainder, 13 edges)
After W1:  W2 (wm_compare, 77 entries)
Deferred:  W4 (browser_engine net cluster) — one-line status below
```
W1/W3 file sets are disjoint; run concurrently. W2 reuses W1's clock port.

---

## W1 — Timer edges in `src/lib` (the largest removable class)

**Value:** each removal is a portability gain toward the 2D+events-only
contract; timers are the class with an obvious portable seam (frame clock).

**Owns (new):** `src/lib/common/ui/ui_frame_clock.spl` (pure port: a
`FrameClock` trait — `now_micros()`, `sleep_until(deadline)` expressed as a
requested-wake value, NO io import — plus a `FixedStepClock` pure test double),
`src/lib/nogc_sync_mut/ui/host_frame_clock.spl` (host adapter implementing the
port via `io.time_ops` — `nogc_sync_mut/ui/` is OUTSIDE the 13 scope dirs, so
the io import is legal there; verify by running the checker, not by assuming),
`test/01_unit/lib/common/ui/ui_frame_clock_spec.spl` (new).
**Owns (edit — the 18 in-scope lib files with timer references, enumerated
2026-08-05):**
browser_engine: `backend_screenshot_capture.spl`, `net/cache.spl`,
`script/js_compat.spl`, `script/timer_api.spl`,
`simple_web_html_engine2d_presenter.spl`,
`simple_web_html_layout_renderer_core.spl`,
`simple_web_html_layout_renderer_foundation.spl`,
`simple_web_html_layout_renderer_paint_layout.spl`,
`simple_web_layout_engine2d_fast.spl` (all under
`src/lib/gc_async_mut/gpu/browser_engine/`);
engine2d: `backend_metal_font.spl`, `backend_metal.spl`,
`backend_session.spl`, `backend_vulkan_font.spl`, `host_ops.spl`,
`vulkan_session.spl`, `web_wm_session.spl`, `wm_frame_pacing.spl` (all under
`src/lib/gc_async_mut/gpu/engine2d/`);
`src/lib/nogc_async_mut/wm/wm_optimization.spl`.
(`src/app/wm_compare/*` timer edges belong to W2, NOT here — ownership is
exclusive.)

**Task:** replace every direct `io.time_ops` / `rt_time_now_*` /
`rt_sleep_nanos` use in the owned in-scope files with the injected `FrameClock`
port (constructor/param injection following each module's existing dependency
style; callers outside scope construct `host_frame_clock`). No behavior
change: same units, same call sites. Files here that carry OTHER violation
classes (e.g. `host_ops.spl` fs/net edges) lose ONLY their timer edges in this
tranche — do not chase other classes.

**Gate:** procedure above; expected post-count: **219 − (timer entries in the
18 owned files)** — compute the exact number FIRST by cross-referencing
baseline entries against timer-import lines, state it in the report, then hit
it exactly. Plus `ui_frame_clock_spec.spl` verdict `failed=0 dropped=0
executed>=4` (FixedStepClock determinism; adapter monotonicity), plus the
behavior-preservation oracle over the mirroring specs (equal counts).
**Sabotage #3 subject:** make `FixedStepClock` return a constant instead of
advancing → its determinism/advance assertion RED.
**Size:** 2 agent-sessions. **Status: dispatchable now.**

## W2 — `wm_compare` (77 entries, the largest concentration)

**Decision made here so the lane needs none:** `wm_compare` is a host-side
measurement harness; its host access is inherent but does NOT belong inside
the scoped dir. Split: portable comparison core stays in
`src/app/wm_compare/`; all host I/O (fs export, capture, process, env, and the
timer edges left out of W1) moves behind adapters in a NEW sibling
`src/app/wm_compare_host/` (outside `wm_lane_scope_dirs`). In-scope files then
import the adapter facade instead of `io.*`/`rt_*` directly. This is a real
boundary, not a lint dodge: the portable core must compile with the adapter
replaced by a stub (that is the sabotage).

**Owns:** every file under `src/app/wm_compare/` that appears in the baseline
(list is the baseline itself, 77 entries), the new `src/app/wm_compare_host/`
dir, plus W1's clock port as a read-only dependency.

**Gate:** procedure above; expected post-count stated exactly before editing
(77 fewer than the pre-tranche count if complete; partial waves allowed but
each wave states and hits its exact number). Behavior oracle: the wm_compare
capture/parity specs and check scripts that already exist (enumerate via
`ls scripts/check/ | /usr/bin/grep wm` — run the ones whose subjects were
touched; record before/after verdict equality). **Sabotage #3 subject:**
replace the host adapter with the stub and confirm the portable core still
LOADS (import resolution proven by which error text changes, not exit status —
unresolved `use` is WARN/exit 0) while capture specs correctly go RED.
**Size:** 3 agent-sessions (largest tranche). **Status: blocked by W1** (uses
the clock port; also avoids double-editing the timer files).

## W3 — Small remainder (13 entries)

**Owns:** `src/lib/nogc_sync_mut/play/wm/mod.spl` (4),
`src/lib/nogc_async_mut/wm/` non-timer entries (1),
`src/lib/common/ui/` entries (2), `src/os/services/wm/wm_codec.spl` (6).
**Task:** per-file: replace the flagged import with the portable equivalent if
one exists (W1's clock; existing 2D/event ports); where the dependency is
genuinely dead, delete the import and any dead code behind it (never convert
TODO→NOTE; delete or implement). `wm_codec.spl` sits in the OS service — if
its 6 edges are load-bearing host calls, the lane reports that with the call
sites and moves them behind the existing WM host seam
(`src/lib/nogc_async_mut/wm/host.spl` is READ-ONLY per the unified-packed-ui
lane doc — file a note rather than editing it; the seam extension belongs to
that doc's owner).
**Gate:** procedure above; expected post-count stated exactly; behavior oracle
over mirroring specs. **Sabotage #3 subject:** re-introduce the `wm_codec`
direct host call → checker FAIL (sabotage #1 covers it; #3 here may reuse #1).
**Size:** 1 agent-session. **Status: dispatchable now.**

## W4 — browser_engine net cluster (h1_client 9, websocket_client 8, ws_handshake 4, cache 3, …)

Deferred in one line: networking is inherent to the browser engine and needs a
designed host-net port (an architecture decision for `browser_engine`, not a
ratchet chore); forcing it through this ratchet would produce a fake seam.
Revisit after W2 proves the adapter-split pattern at scale.
