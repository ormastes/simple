# WM Platform Honesty — Parallel-Agent Execution Lanes

Status: plan (dispatch document). Covers Task #59 (31 false-success stubs),
Task #60 (FreeBSD WM seam), and the SDL2 seam-subset audit.

Evidence authority (read before starting any lane — these are FINDINGS, this
file is the PLAN):

- `doc/04_architecture/ui/wm_host_platform_matrix.md` — the 5-platform audit.
  Its "False-success stubs, ranked" section IS the family enumeration for
  Task #59: **31 sites in 6 clusters (0–5), each with file:line**. Lanes below
  reference sites by that doc's numbering (0a–0d, 1–27). Do not re-derive.
- `doc/04_architecture/ui/wm_gui_web_dependency_audit.md` — 184 violations /
  5-edge legitimate surface; timers already classified the largest removable
  class (22 edges, class C "hidden precondition").
- `doc/03_plan/ui/unified_packed_ui_scene_agent_lanes.md` — sibling lane plan.
  Its lanes hold `src/lib/nogc_async_mut/wm/host.spl` **read-only**; lane A2
  below is the sole writer of that file across both plans.

What existing docs already cover (do not duplicate):
- The stub *enumeration* and dangling-extern table: fully covered by the
  platform matrix. This plan adds only the fix lanes and guards.
- The *timer/violation classification*: fully covered by the dependency audit.
  Lane C consumes it; it does not re-classify.
- The FreeBSD *refusal vocabulary*: already implemented — `host.spl` trait
  `WmHost2d` (4 methods: `surface_acquire`, `surface_present`,
  `surface_release`, `event_poll`), `WmHost2dUnavailable`, and
  `wm_host_2d_for("freebsd")` already returns
  `unavailable("freebsd", "VM harness boots but no 2D backend exists...")`.
  Lane B verifies and documents it; it does not re-design it.

## Governing rule (applies to every fix in this plan)

**A capability flag must be backed by a real implementation or report false.**
A handle must come from something opened, or not be returned. A "presented"
status must follow bytes moving, or be a refusal. `WmHost2dUnavailable` /
`wm_host_status(false, reason)` / `Err(...)` / `nil` are the established
honest-refusal vocabulary — use them; do not invent new sentinels.

**The fix direction for every site in Task #59 is honest refusal, NOT native
implementation.** Implementing real Cocoa/Win32/X11 backends is explicitly out
of scope for these lanes (mac/win cannot even be executed from this host).

## Ground rules for every lane (non-negotiable)

1. **File ownership is exclusive.** A lane writes ONLY the paths in its "Owns"
   list. Concurrent lanes have silently clobbered each other three times this
   session. If a lane needs a change in a file it does not own, it reports the
   need; the owning lane makes the change. Before dispatch, cross-check the
   packed-UI plan's owns-lists; the only intentional cross-plan contact is
   `host.spl` (read-only there, owned by A2 here).
2. **Gate discipline.** Capture the full run to a file. The authoritative
   receipt is the stderr/stdout line
   `SPEC FILE VERDICT: <path> declared>=N executed=N passed=N failed=N dropped=N`.
   Match with `/usr/bin/grep -a "SPEC FILE VERDICT"` (lines are
   ANSI-colour-wrapped; NEVER `tail -1`; never anchor a numeric regex at line
   start — `^[0-9]+ examples` matches nothing). A gate passes only when
   **executed >= the lane's declared floor AND failed=0 AND dropped=0** —
   compare COUNTS, not just failures; a module-load failure drops whole
   describes at exit 0. Run with `--no-cache --no-cover-check` (concurrent
   lanes race the shared manifest into "0 total" at exit 0 otherwise). Exit
   255/143 with no output = timeout/kill, not a verdict. Exit status is
   FAIL-OPEN (an unresolved `use` is only a WARN at exit 0); the verdict line
   is the only oracle. No bare `assert` (inert); no `check(true)` (vacuity
   invisible to an `expect(` scan); `pending()` never registers a failure and
   never satisfies an executed floor.
3. **Sabotage check is mandatory before declaring a lane done.** Apply the
   listed sabotage, re-run the gate, confirm `failed>=1` (or the executed
   floor breaks), revert, re-confirm green. A gate that stays green under
   sabotage is a lane FAILURE, not a pass. Sabotage the IMPLEMENTATION, never
   a shim or fixture — this repo has shipped a guard that matched only its own
   fixture.
4. **Platform executability.** This host is Linux. macOS and Windows **cannot
   be executed** — any assertion about their native-true path is static-only
   (grep/structure), and the lane's report MUST NOT claim a green runtime
   verdict for them. FreeBSD CAN be executed
   (`sh scripts/check/check-freebsd-bootstrap-qemu.shs --smoke`; verified
   FreeBSD 14.4, clang OK). SimpleOS can, under real firmware only — `-kernel`
   and `isa-debug-exit` are forbidden (`.claude/rules/board-runnable.md`).
5. **WML001/WML002 ratchet.** Every lane runs `bin/simple lint <its touched
   .spl files>` and adds **zero** entries beyond the 219-entry baseline
   (`doc/08_tracking/wm_lane_boundary_baseline.txt`). Fix lanes may REMOVE
   entries; removals update the baseline in the same commit.
6. **Blast radius is part of the lane.** Flipping a fabricated success to a
   refusal breaks every spec that asserted the fabrication (known instance:
   `test/03_system/app/simpleos/feature/simpleos_wine_proton_steam_impl_spec.spl:203-209`
   passes against counter handles). Each fix lane greps for callers/specs of
   every function it changes, updates their expectations to assert refusal,
   and lists them in its report. Leaving a sibling spec asserting the old lie
   is lane failure.
7. **Commit + push per lane immediately on green** (plumbing CAS per repo VCS
   rules); grep-verify file content before committing — a parallel process can
   revert files mid-session.

## Lane graph

```
Wave 0 (dispatchable now):  A0 family-guard   B freebsd   C sdl2-subset
Wave 1 (after A0):          A1 dispatch   A2 wm-core   A3 gpu   A4 input   A5 rust-crate
```

A1–A5 are mutually independent (disjoint files) — run concurrently. They are
blocked by A0 only because they must delete entries from the baseline file A0
creates (single-writer-per-file rule; A0 hands the file over lane-by-lane via
its report — in practice: each Wave-1 lane owns exactly its own lines of the
baseline file, and edits only those lines, which is safe because line sets are
disjoint). B and C touch no Wave-1 file.

---

## A0 — False-success family guard (enumeration ratchet)

**Why first:** the standing rule is that a sweep which does not enumerate the
family leaves siblings behind. The matrix enumerated 31 sites *once*; this
lane freezes that as a machine-checked baseline so (a) new siblings cannot
land silently, (b) each fix lane's progress is measured by baseline shrink.

**Owns (new files only):**
- `doc/08_tracking/wm_false_success_baseline.txt` — one line per open site:
  `<path>:<matrix-site-id>:<predicate-tag>`; initial content = the 31 sites.
- `test/03_system/gui/wm_host_platform/wm_false_success_family_spec.spl`

**Task:** the spec runs anchored searches over non-vendored source (pin
`/usr/bin/grep`; exclude `src/*/vendor/**` and the three stb/miniaudio
headers) for these predicate families, and asserts every match is listed in
the baseline:
1. `uses_native_[a-z0-9_]*_symbols` whose body is literal `true`
   (multi-line-aware: fn line + next non-comment line).
2. `readback()` bodies returning the `""` success sentinel in
   `src/lib/gc_async_mut/gpu/session/backend_*_adapter.spl`.
3. `engine2d_readback(.*"cpu_mirror")` reachable unconditionally (no
   enclosing availability `if`) in `backend_webgpu.spl`.
4. Counter-handle returns: `_ctr + 1` / `.len() + 1` used as a return value in
   `src/lib/nogc_async_mut/wm/*.spl`, `src/os/compositor/hosted_backend*.spl`,
   `src/lib/nogc_async_mut/gpu/dxvk_d3d11.spl`.
5. `supports_[a-z_]*\(\)` / `supports(` bodies hardcoding `true` in the same
   file sets.
A match not in the baseline = FAIL (new sibling). A baseline line with no
match = FAIL (stale line — the fixing lane must delete it in the same commit
as the fix). The spec also asserts baseline line count is printed in the
verdict body, so the shrink is visible per run.

**Gate:**
```
bin/simple test test/03_system/gui/wm_host_platform/wm_false_success_family_spec.spl \
  --no-cache --no-cover-check > /tmp/a0.log 2>&1
/usr/bin/grep -a "SPEC FILE VERDICT" /tmp/a0.log
```
Receipt: one verdict line, `executed>=6 failed=0 dropped=0` (one example per
predicate family plus one baseline-consistency example).

**Sabotage (both must go RED individually):**
1. Add a scratch file `src/os/compositor/zz_sabotage.spl` containing
   `static fn uses_native_zz_symbols() -> bool:\n    true` → predicate 1 finds
   an unlisted match → RED. Delete the file after.
2. Delete one line from the baseline while its site is still unfixed → RED
   (stale-detection direction proves the guard reads real source, not its own
   fixture).

**Dispatchable now.** **Size (estimate):** 1 agent-session, ~250–400 lines.

---

## A1 — Cluster 0: host-backend dispatch & capability self-report (sites 0a–0d)

**Owns:** `src/os/compositor/hosted_backend_cocoa.spl`,
`src/os/compositor/hosted_backend_win32.spl`,
`src/os/compositor/hosted_backend.spl`,
`src/os/compositor/hosted_backend_gui_renderer.spl`,
new `test/03_system/gui/wm_host_platform/hosted_backend_honesty_spec.spl`,
its own lines of `doc/08_tracking/wm_false_success_baseline.txt`.

**Task:**
- 0a/0b: `uses_native_cocoa_symbols()` / `uses_native_win32_symbols()` must
  return the truth of the build: probe the underlying FFI (the honest C shims
  return `-1` when not compiled native — call a cheap probe symbol once and
  cache) or gate on the platform report the runtime already exposes. On this
  Linux host both MUST return `false`. Keep the honest `try_create` guards
  (`cocoa:40-53`, `win32:39-52`) untouched — the matrix certified them.
- 0c (`hosted_backend.spl:222,228`): the synthetic winit buffer handle — the
  `rt_winit_buffer_*` family has NO native definition (interpreter-only, per
  the matrix's dangling-extern table). Return `nil`/failure status when the
  extern did not produce a real buffer, instead of fabricating a handle.
- 0d (`hosted_backend_gui_renderer.spl:15-20`): `create` with an empty pixel
  store must return `nil` (refusal), or allocate the real `w*h` store if that
  is its actual contract — decide by reading its single caller; if the caller
  treats pixels as a framebuffer, refusal is correct until a real store exists.

**Gate:**
```
bin/simple test test/03_system/gui/wm_host_platform/hosted_backend_honesty_spec.spl \
  --no-cache --no-cover-check > /tmp/a1.log 2>&1
/usr/bin/grep -a "SPEC FILE VERDICT" /tmp/a1.log
```
Receipt: `executed>=6 failed=0 dropped=0`. Required assertions:
(a) `uses_native_cocoa_symbols()` is `false` on this host (executable —
runtime assertion); (b) same for win32; (c) creating a hosted buffer without a
live winit backing yields refusal, not a handle; (d) gui-renderer `create`
never returns a backend whose pixel store length is 0 while reporting
success; (e) static: `/usr/bin/grep -A2 "uses_native_cocoa_symbols"` shows no
literal `true` body (this is the ONLY form of mac-side verification allowed —
the mac-native `true` path is static-only, no green runtime claim); (f) same
for win32.

**Sabotage:** revert 0a to literal `true` → assertions (a) and (e) RED; A0's
guard must ALSO go RED on the same revert (run it once to confirm the ratchet
sees regressions — this is the cross-check that A0 is not fixture-bound).
**Blocked by A0.** **Size (estimate):** 1 agent-session, ~150 changed lines +
~200 spec lines.

---

## A2 — Clusters 1+2: WM core tier and the host seam's Linux lie (sites 1–10)

**Owns:** `src/lib/nogc_async_mut/wm/host.spl` (sole writer across BOTH lane
plans — see header), `src/lib/nogc_async_mut/wm/service.spl`,
`src/lib/nogc_async_mut/wm/compositor.spl`,
`src/lib/nogc_async_mut/wm/input.spl`,
`src/lib/nogc_async_mut/wm/wm_optimization.spl`,
existing `test/01_unit/lib/nogc_async_mut/wm/host_seam_spec.spl`,
`test/01_unit/lib/nogc_async_mut/wm/compositor_spec.spl`,
`test/01_unit/lib/nogc_async_mut/wm/input_spec.spl`,
`test/03_system/app/simpleos/feature/simpleos_wine_proton_steam_impl_spec.spl`
(blast-radius updates only), its baseline lines.

**Task:**
- Site 1: `impl WmHost for WmHostLinux` — `supports()` returns `false` for all
  ten capabilities (nothing real backs any of them; the matrix confirmed zero
  X11/Wayland symbols in non-vendored source). `port_open`/`present`/
  `clipboard_*` return the refusal vocabulary. If test code needs the
  in-memory behavior, it must construct the existing `WmHost2dReference` /
  a renamed `WmHostSimulated` explicitly — a type named `WmHostLinux` may not
  simulate.
- Site 2: `WmHostSimpleOs.present` returns `wm_host_status(false,
  "unsupported:present — no framebuffer bound; use wm_host_2d_for_backed")`,
  matching the file's own docstring promise.
- Site 3: `WmHostSimpleOs.now_micros` frozen clock — either wire a real time
  source through the backed seam or make the frame report's `clock_advanced`
  check require strict `t1 > t0` so a frozen clock reads unhealthy. Choose the
  latter unless a time source already flows through `wm_host_2d_for_backed`.
- Sites 4–10: `service.spl` / `compositor.spl` / `input.spl` /
  `wm_optimization.spl` — every counter-handle and `ok:true` fabrication
  becomes a refusal unless a real backend was injected. Follow the seam
  pattern: keep the pure logic, move "success" behind an injected `WmHost2d`
  (or equivalent) that only `wm_host_2d_for_backed` can supply.
- Blast radius (rule 6): update the Wine/Proton/Steam spec to assert refusal;
  enumerate all other callers of `wm_port_open`/`wm_window_create`/
  `wm_compositor_window_present`/`wm_input_poll` and update each.

**Gate:**
```
bin/simple test test/01_unit/lib/nogc_async_mut/wm/host_seam_spec.spl \
  test/01_unit/lib/nogc_async_mut/wm/compositor_spec.spl \
  test/01_unit/lib/nogc_async_mut/wm/input_spec.spl \
  test/03_system/app/simpleos/feature/simpleos_wine_proton_steam_impl_spec.spl \
  --no-cache --no-cover-check > /tmp/a2.log 2>&1
/usr/bin/grep -a "SPEC FILE VERDICT" /tmp/a2.log
```
Receipt: four verdict lines, each `failed=0 dropped=0`, combined
`executed>=25` (floor: the three unit specs' current example counts must not
shrink — record the pre-change executed counts first and use them as the
per-file floor; a count DROP is a red flag for a module-load failure).
Required new assertions: (a) `WmHostLinux.supports(cap)` is `false` for all
ten capabilities; (b) `wm_port_open()` without a backend refuses; (c) the
Wine spec asserts refusal where it asserted counter-success; (d)
`wm_host_2d_frame` health check fails on a frozen clock.

**Sabotage:** re-hardcode `supports() -> true` for one capability → (a) RED;
restore `port_open`'s counter return → (b) RED. Both individually.
**Blocked by A0.** **Size (estimate):** 2 agent-sessions, ~400 changed lines +
~300 spec lines. Highest blast radius of the plan — budget for caller sweep.

---

## A3 — Cluster 3: GPU backends and session adapters (sites 11–20)

**Owns:** `src/lib/gc_async_mut/gpu/engine2d/backend_webgpu.spl`,
`src/lib/nogc_async_mut/gpu/dxvk_d3d11.spl`,
`src/lib/nogc_async_mut/gpu/vulkan_icd_sffi.spl`,
`src/lib/gc_async_mut/gpu/session/backend_metal_adapter.spl`,
`.../backend_webgpu_adapter.spl`, `.../backend_vulkan_adapter.spl`,
`.../backend_cuda_adapter.spl`, `.../backend_cpu_adapter.spl`,
`src/lib/gc_async_mut/gpu/engine2d/engine.spl` (one change: see below),
new `test/01_unit/lib/gc_async_mut/gpu/session/adapter_honesty_spec.spl`,
its baseline lines.

**Task:**
- Site 11 (`backend_webgpu.spl:277`): `init()` returns the availability
  result, not a bare `true`; `initialized` may only be set when
  `gpu_ready` is.
- Site 12 (`:561`): `read_pixels_with_source` reports `"cpu_mirror"` truthfully
  today — the lie is upstream consumers treating it as device readback. Keep
  the truthful source string, and close the hole where it is believed:
- Sites 13, 14: `dxvk_d3d11.spl:184` device handle from `len()+1` with zero
  externs → return failure/`nil`; `vulkan_icd_sffi.spl:103-108` uncondition-
  al `_icd_ok` → gate on the real ICD probe result.
- Sites 15–19: all five adapters' `readback()` returning `""` (success
  sentinel) with zero pixels moved → return an explicit error string /
  refusal for the adapters with no real device path on this host; the CPU
  adapter may succeed only if it actually copies its buffer.
- Site 20: `backend_metal_adapter.spl:49,52,55` `supports_* -> true` → gate on
  `is_macos()`-equivalent AND real symbol availability; on this host: `false`
  (static-only for the mac-true side, rule 4).
- Mitigation unification (`engine.spl`): the matrix found the readback-source
  check lives ONLY in `detect_best_backend_viable()` (`:910/:948`) while
  default `detect_best_backend()` (`:879`) skips it. Make the default path
  apply the same viability check (or delegate to `_viable`). This single
  change closes the "separate unchecked entry point" hole; touch nothing else
  in engine.spl.

**Gate:**
```
bin/simple test test/01_unit/lib/gc_async_mut/gpu/session/adapter_honesty_spec.spl \
  --no-cache --no-cover-check > /tmp/a3.log 2>&1
/usr/bin/grep -a "SPEC FILE VERDICT" /tmp/a3.log
```
Receipt: `executed>=8 failed=0 dropped=0`. Required assertions: (a) webgpu
`init()` on a host without WebGPU returns `false` and `probe_backend` does not
report initialized; (b) dxvk device creation without externs refuses; (c) each
no-device adapter `readback()` returns non-`""`; (d) metal adapter
`supports_compute()` is `false` on this host; (e) `detect_best_backend()` and
`detect_best_backend_viable()` agree on rejecting a backend whose readback
source is `cpu_mirror` (construct the stub backend in-spec — but assert
against the REAL engine functions, not a local copy of them; import from
`std.gc_async_mut.gpu.engine2d`, shim vacuity is a known failure mode here).

**Sabotage:** restore the bare `true` at the end of `init()` → (a) RED;
make `detect_best_backend` skip the viability check again → (e) RED.
**Blocked by A0.** **Size (estimate):** 1–2 agent-sessions, ~200 changed
lines + ~250 spec lines. Blast-radius note: specs that currently pass because
webgpu "initializes" on CPU must be swept (rule 6).

---

## A4 — Cluster 4: input event sources (sites 21–25)

**Owns:** `src/os/compositor/hosted_input_backend.spl` (sites 21, 22 ONLY —
the two FreeBSD docstring lines in this file belong to lane B; coordinate by
dispatching B first or same-agent), `src/os/compositor/hosted_input_sdl2.spl`,
`src/os/compositor/arm64_virtio_input_backend.spl`,
new `test/01_unit/os/compositor/hosted_input_honesty_spec.spl`,
its baseline lines.

**Task:**
- Site 21: `_build_mouse_event` hardcoded `dx:0, dy:0` → compute real deltas
  from last position, or mark the event `has_delta: false` honestly.
- Site 22: `rt_winit_event_mouse_button` declared `(i64,bool)` vs runtime's
  `i64` → fix the declaration to match the runtime's actual signature and
  decode pressed-ness explicitly.
- Sites 23, 24: `hosted_input_sdl2.spl` — 3 of 6 externs dangling, zero call
  sites anywhere in `src/`, and a keymap sending every lowercase letter to
  `Key.A`. **Delete the file** (it cannot work and nothing imports it) rather
  than fix dead code; NOTE the deletion in the report and delete its baseline
  lines. If deletion is vetoed, honest refusal + real keymap; but the default
  is delete. Caution: delete-verification by exit status is FAIL-OPEN
  (unresolved `use` is a WARN) — verify no importer by anchored grep, not by
  a green build.
- Site 25: `arm64_virtio_input_backend.spl:90-95` — dangling
  `rt_arm64_virtio_input_poll` reads as idle → make poll report
  "backend unavailable" when the extern is unresolved instead of an empty
  queue.

**Gate:**
```
bin/simple test test/01_unit/os/compositor/hosted_input_honesty_spec.spl \
  --no-cache --no-cover-check > /tmp/a4.log 2>&1
/usr/bin/grep -a "SPEC FILE VERDICT" /tmp/a4.log
```
Receipt: `executed>=5 failed=0 dropped=0`. Assertions: (a) mouse event carries
real or honestly-flagged deltas (two sequential positions produce nonzero dx);
(b) mouse-button decode matches the runtime's `i64` shape; (c) anchored grep
proves `hosted_input_sdl2.spl` is gone AND no source references it; (d) virtio
poll without the extern reports unavailable, not idle.

**Sabotage:** re-hardcode `dx: 0` while feeding moving positions → (a) RED;
re-create an empty `hosted_input_sdl2.spl` stub → (c) RED.
**Blocked by A0** (and orders after B for the shared file — B is Wave 0, so in
practice not a delay). **Size (estimate):** 1 agent-session, ~120 changed
lines + ~180 spec lines.

---

## A5 — Cluster 5: Rust host crate (sites 26–27) — mini-lane

Two sites only; does not warrant a full lane apparatus, but Rust means the
sspec gate does not apply, so it gets its own mini-gate.

**Owns:** `src/runtime/hosted/webgpu.rs`, `src/runtime/hosted/select.rs`,
its baseline lines.

**Task:** Site 26: `shutdown()` "pretend succeeded" → return `false` in stub
mode (callers treating teardown as idempotent must tolerate it — sweep the
crate's callers). Site 27: `select.rs` — unknown `SIMPLE_HOSTED_SURFACE`
values and the linux/freebsd/simpleos absence silently fall through to
`SEL_WINIT` → add an explicit error/refusal arm (log + a sentinel the Simple
layer maps to refusal); document the accepted values in the match.

**Gate:** `bin/simple build check > /tmp/a5.log 2>&1; echo "exit=$?"` —
receipt is `exit=0` AND a `cargo test` case added in the crate asserting an
unknown surface value does NOT select `SEL_WINIT`
(`/usr/bin/grep -a "test result:" /tmp/a5.log` shows `0 failed` with the new
test named in the run — verify the test RAN by name, not just overall green).
**Sabotage:** restore the silent fallthrough → the new cargo test RED.
This is Rust-side by necessity (the defect is in Rust); "fix .spl not Rust"
does not apply to a Rust-crate defect.
**Blocked by A0.** **Size (estimate):** 0.5 agent-session, ~40 changed lines.

---

## B — Task #60: FreeBSD WM seam (decision + verification lane)

**Decision: honest explicit refusal is the right first step — and it already
exists.** Justification: (1) the seam (`host.spl`) already routes
`wm_host_2d_for("freebsd")` to `WmHost2dUnavailable` with an accurate reason —
the refusal vocabulary was designed for exactly this; (2) a real FreeBSD 2D
backend would be built on SDL2/X11 arms that do not exist for LINUX yet —
implementing FreeBSD's before the primary host's inverts priority and would be
over-engineering; (3) the only actual LIES are two docstrings. What is
genuinely new here vs mac/win: FreeBSD refusal can be **executed and verified
on the real platform** via the QEMU harness, so this lane produces the plan's
only cross-platform runtime receipt. Real implementation is recorded as an
explicit non-goal, unblocked-by "a real hosted 2D backend existing for Linux
first" — file it as a follow-up line in the matrix doc when this lane lands.

**Owns:** the two docstring lines of
`src/os/compositor/hosted_input_backend.spl` (`:4`, `:152` — ONLY those lines;
the rest of the file is lane A4's),
new `test/03_system/gui/wm_host_platform/wm_host_freebsd_refusal_spec.spl`,
new `scripts/check/check-freebsd-wm-seam-refusal.shs`.

**Task:**
1. Fix the two docstrings: remove FreeBSD from the claimed-support list (or
   state "FreeBSD: no arm exists; seam refuses"). A docstring is the cheapest
   possible false-success.
2. Linux-side spec: assert `wm_host_2d_for("freebsd")` returns platform
   `"freebsd"` with a refusal reason mentioning the missing backend; assert
   all four `WmHost2d` methods on the refusal answer unavailable (not green);
   anchored-grep assert no non-vendored source claims FreeBSD WM support
   outside the refusal vocabulary.
3. FreeBSD-side probe: `check-freebsd-wm-seam-refusal.shs` wraps the existing
   `check-freebsd-bootstrap-qemu.shs` plumbing (same VM lifecycle), copies a
   minimal probe over ssh, executes it in-VM, and captures a transcript. The
   probe prints exactly one line:
   `FREEBSD WM SEAM VERDICT: platform=<detected> refusal=<yes|no> reason=<...>`
   Pass requires `platform=freebsd refusal=yes` AND the transcript containing
   the in-VM `uname -srm` line (board-evidence bar: identity + boot path +
   transcript). If the probe binary cannot be built for FreeBSD yet, run the
   probe via the interpreted path built in-VM by the smoke bootstrap; if THAT
   is unavailable, the lane reports **blocked by FreeBSD in-VM execution of
   Simple code** with the transcript proving the attempt — it does not
   downgrade to Linux-only green silently.

**Gate:**
```
bin/simple test test/03_system/gui/wm_host_platform/wm_host_freebsd_refusal_spec.spl \
  --no-cache --no-cover-check > /tmp/b1.log 2>&1
/usr/bin/grep -a "SPEC FILE VERDICT" /tmp/b1.log
sh scripts/check/check-freebsd-wm-seam-refusal.shs > /tmp/b2.log 2>&1
/usr/bin/grep -a "FREEBSD WM SEAM VERDICT" /tmp/b2.log
```
Receipt: verdict line `executed>=4 failed=0 dropped=0` AND the
`FREEBSD WM SEAM VERDICT: platform=freebsd refusal=yes ...` line from a
transcript that also contains `uname` output. Both halves required.

**Sabotage:** temporarily make the freebsd arm of `wm_host_2d_for` return
`wm_host_2d_reference(...)` disguised as available (coordinate the temporary
edit with lane A2, host.spl's owner — or run B's sabotage before A2 dispatch)
→ the Linux spec's refusal assertion RED AND the in-VM probe prints
`refusal=no` → RED. Restore, re-confirm green.
**Dispatchable now** (QEMU harness verified working from this host).
**Size (estimate):** 1 agent-session, ~30 changed lines + ~150 spec/script
lines + one VM round-trip (~15–30 min wall time).

---

## C — SDL2 seam-subset audit (answer + ratchet)

**The open question this lane answers:** does the WM/compositor path use only
the seam-shaped subset of SDL2 (2D surface + events), or does it reach the
extras? The registered SDL2 surface is ~66 entry points; the seam is 4
methods. Extras (timers — `get_ticks_ms`; display bounds/DPI; window
title/size/position/fullscreen; cursor grab/warp) are hidden preconditions
(class C in the dependency audit; timers already ranked the largest removable
class at 22 edges). Only 3 of the 14 `.spl` SDL2 callers are compositor
(`src/os/compositor/hosted_backend_sdl2.spl`, `hosted_input_sdl2.spl` — note
A4 will likely DELETE that one — and `hosted_backend.spl`); the rest are
`game2d` (2), `web_ui` (4), `desktop/display`, `io/window_sffi`,
`app/io` (2), which legitimately may want full SDL2. So "is SDL2 needed" gets
a per-consumer answer, not a blanket one.

**Owns (new files only):**
- `doc/04_architecture/ui/sdl2_seam_subset_audit.md` (findings doc)
- `doc/08_tracking/wm_sdl2_extras_baseline.txt`
- `test/03_system/gui/wm_host_platform/sdl2_seam_subset_spec.spl`

**Task:**
1. Enumerate the registered surface: anchored grep of `rt_sdl2_[a-z0-9_]*`
   definitions in `src/runtime/runtime_sdl2.c` and
   `src/compiler_rust/compiler/src/interpreter_extern/sdl2.rs`; the audit doc
   records the exact count (expected ~66 — report the measured number, do not
   copy this estimate) and tags each entry `seam:surface`, `seam:event`, or
   `extra:<timer|display|window-mgmt|cursor|other>`.
2. Per-caller matrix: for each of the 14 callers, which entry points it
   touches, and the verdict: `seam-only` / `extras:<list>` / `full-SDL2
   consumer (out of contract scope)`. Compositor callers get the strict
   verdict; `game2d`/`web_ui`/`desktop`/`app/io` are recorded as legitimate
   full-surface consumers and explicitly excluded from the ratchet.
3. Ratchet spec: asserts that files under `src/os/compositor/` and
   `src/lib/nogc_async_mut/wm/` reference NO `rt_sdl2_*` symbol outside the
   allowlist `{poll_event, event_* accessors, present_rgba, create_window,
   destroy_window}` except entries in the extras baseline. Baseline starts at
   the current measured extras (expected to include `get_ticks_ms`); shrink
   only. This gives the timer-class removal (dependency-audit class C) a
   compositor-scoped enforcement point without re-litigating the whole
   184-violation list.
4. One recommendation section in the audit doc: for each baseline extra,
   the seam-shaped replacement (e.g. `get_ticks_ms` → clock injected via the
   backed seam, per lane A2 site-3 handling) — recommendation only, no code.

**Gate:**
```
bin/simple test test/03_system/gui/wm_host_platform/sdl2_seam_subset_spec.spl \
  --no-cache --no-cover-check > /tmp/c1.log 2>&1
/usr/bin/grep -a "SPEC FILE VERDICT" /tmp/c1.log
```
Receipt: `executed>=4 failed=0 dropped=0` (surface-count example, allowlist
example, baseline-consistency example, out-of-scope-exclusion example).

**Sabotage:** add `rt_sdl2_get_ticks_ms` (or any unlisted extra) reference in
a scratch file under `src/os/compositor/` → RED; remove a baseline line whose
extra is still referenced → RED (stale direction). Both individually; delete
scratch after.
**Dispatchable now.** No production code changes — audit + guard only, so no
WML ratchet exposure beyond lint on the new spec.
**Size (estimate):** 1 agent-session, ~250 doc lines + ~150 spec lines.

---

## Judged NOT worth a lane (recorded so silence is not ambiguity)

- **Implementing real macOS/Windows native backends** — cannot be executed or
  verified from this host; any such lane would end in an unverifiable green.
  Out of scope until a mac/win runner exists.
- **Implementing a real Linux X11/Wayland/SDL2 `WmHost2d` backend** — real
  work, but a separate design effort (backend choice, headless-host
  constraint: this host has no `DISPLAY`/`WAYLAND_DISPLAY`). Not a honesty
  fix; do not smuggle it into A2. Needs its own design doc first.
- **Re-fixing the dangling-extern WARN-only policy** (fail-open `use`) — a
  compiler/lint concern far wider than WM; tracked elsewhere.
- **The 184-violation dependency cleanup** — already has its own audit doc and
  classification; lane C adds the compositor-scoped ratchet only.
- **`wm_optimization.spl` beyond site 10** — one line in A2's sweep, not a
  lane.

## Dispatch summary

| Lane | Scope | Status |
|---|---|---|
| A0 | family enumeration guard + baseline | **dispatchable now** |
| A1 | cluster 0 (compositor dispatch, 4 sites) | blocked by A0 |
| A2 | clusters 1+2 (wm core + host seam, 10 sites) | blocked by A0 |
| A3 | cluster 3 (GPU/adapters, 10 sites) | blocked by A0 |
| A4 | cluster 4 (input, 5 sites) | blocked by A0 |
| A5 | cluster 5 (Rust crate, 2 sites) | blocked by A0 |
| B | FreeBSD refusal verification | **dispatchable now** |
| C | SDL2 seam-subset audit + ratchet | **dispatchable now** |
