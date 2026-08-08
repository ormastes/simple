# Plan: Default-on precompiled+cached SMF for tui/ui/gui/web/2d lib parts

**Status:** DRAFT — **gated on a NO-GO** (2026-07-06) · **Owner:** UI/perf
**Reads-with (research):** [`doc/01_research/ui/perf/smf_default_ui_caching_research.md`](../../../01_research/ui/perf/smf_default_ui_caching_research.md)
**Reads-with (arch):** [`doc/04_architecture/ui/low_dependency_ui_dynsmf.md`](../../../04_architecture/ui/low_dependency_ui_dynsmf.md),
[`doc/04_architecture/format/smf_specification.md`](../../../04_architecture/format/smf_specification.md)
**Sibling plan:** [`doc/03_plan/ui/rendering/backend_isolation_plan.md`](../rendering/backend_isolation_plan.md)

**Bottom line:** the research verdict is **NO-GO** — the dynSMF load path executes no
code, the perf premise (0.8 ms/char) is falsified for the run lane, and ROI is negative.
This plan therefore does **not** authorize flipping any module id to default-on. It defines
the **two reopen-gates** (P0) that must pass before P1 rollout is even measurable, the exact
conditional rollout set (P1) to try *first* when/if those gates pass, hardening (P2), the
blockers to file (P3), and the non-goals. Nothing in P1–P2 is actioned while P0 is red.

---

## P0 — Reopen-gate acceptance criteria (must pass before ANY rollout)

The NO-GO stands until **both** gates below are green with committed evidence.

### Gate 1 — Execution-wiring proof (blocker; research §1.2)
A dynSMF-"loaded" id must **execute code from the artifact**, not just validate `SMF\0`
magic. Concretely: `smf_dlsym` must resolve a symbol against the artifact's real symbol
table and a call through the resolved address must run loaded code, wired to the native
`ModuleLoader::load` (`src/compiler_rust/runtime/src/loader/loader.rs:16-36`). Evidence: a
spec that loads an SMF, calls an exported function, and asserts a value that could only come
from executed loaded code (not from the text registry in `dynsmf_session.spl:316-322`).

### Gate 2 — Measured parse-avoidance win (research §3)
On a representative lane, an SMF-loaded module must show a **≥ threshold** wall-time
improvement vs the interpret-source baseline, measured 3-run median. **Threshold (from the
win model): the target-lane improvement must be ≥ 0.30 s AND ≥ 10 % of that lane's
baseline.** If the best real measurement is below this, the NO-GO is confirmed and P1 does
not proceed. (Rationale: the derived run-lane parse cost is ≤0.22 µs/char, so anything below
0.30 s is inside measurement noise and below the build-cost amortization line.)

### Baseline table (copy-in; from `smf_perf_baseline.md`)

| Lane | Command | Median |
|---|---|---|
| Browser snapshot | `SIMPLE_EXECUTION_MODE=interpret sh scripts/check/check-macos-metal-browser-backing-evidence.shs` | 6.478 s |
| Small UI spec | `SIMPLE_EXECUTION_MODE=interpret bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_order_spec.spl` | 0.457 s |
| CLI cold run | `bin/simple run examples/01_language/hello.spl` | 0.125 s |
| Browser closure | browser_engine 1916 KB + engine2d 1480 KB | 3396 KB |

### Correctness gates (must stay green regardless of verdict)
- dynSMF dependency-gate spec green
  (`test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl`).
- dynSMF session/policy specs green (`test/01_unit/os/smf/*`,
  `test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl`,
  `test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl`).
- `--dynsmf-status` is **honest**: it must report a loaded id as loaded only when Gate 1's
  executed-code path succeeded, never on magic-only validation.
- **Stale-artifact test (correctness anchor):** EDIT a covered source file → the next run
  must **NOT** serve the stale SMF. Content-hash sidecar (`.srchash`,
  `dynsmf_session.spl:181-193`) already provides the mechanism; the test asserts the mutated
  behavior is observed (fall back to source or rebuild), never the pre-edit result.

---

## P1 — Conditional rollout set (only if P0 both-green)

Flip module ids to default-on **one at a time, leaf-first, highest-parse-cost-first**,
respecting the arch doc's boundaries VERBATIM. Order and rationale:

| # | Module id | Source | Why this order | Gate constraint |
|---|---|---|---|---|
| 1 | `ui-model` (**new** id for `src/lib/common/ui/*` contract layer) | `common/ui/*` | Largest shared parse surface; pure contracts, no backend code (research §5) | Must stay contract-only; must NOT import any backend impl (arch doc §"Common UI Contracts") |
| 2 | `render2d` (existing) | `engine2d/backend_lane.spl` | Already default-on; measure real win on the lane-contract file before widening | Lane-selection only; no per-backend GPU files (no platform field yet — P3) |
| 3 | `tui_renderer` (existing) | widen from the 8-line shim toward `app.ui.tui/backend.spl` closure | Real TUI parse surface; leaf terminal lane | Must NOT reach `app.ui.web`/`browser`/`html_widgets`/`css` — dependency-gate forbidden-prefix list (`..._dependency_gate_spec.spl:87-92`) |

**Excluded from P1 (arch doc excludes them or independent blockers — propose an arch change
separately, do NOT silently widen):**
- `gui_renderer` — currently points at a *web* file; a real native-GUI id needs the
  `SIMPLE_EXECUTION_MODE=interpret` graphics constraint resolved first (research §4). File an
  arch-change request, do not repurpose the id.
- `web_renderer` / `ui_html` beyond the HTML widget layer — the real browser engine is
  blocked by the quadratic 336 KB-CSS hang and self-hosted parser gaps, independent of
  dynSMF. Keep HTML/CSS as **lazy, non-default** capabilities per the gate spec
  (`:134-142`); widening to `browser/backend.spl`/`css.spl` would risk pulling HTML/CSS into
  TUI/CLI paths transitively.
- Per-backend GPU files (vulkan/metal/cuda/...) — mutually exclusive at runtime and need a
  platform/arch field the manifest schema lacks (P3 Gap 2).

**Default-flip mechanism.** Change is confined to the autoload policy: set
`default_autoload` on the target entry in `dynsmf_default_manifest`
(`src/os/smf/dynsmf_session.spl:69-78`). For the new `ui-model` id, add one
`DynSmfManifestEntry` (index-loop-safe; do NOT introduce a `for x in [Struct]` iteration —
Cranelift struct-array bug, research §4) with source
`src/lib/common/ui/<entry>.spl`, output `build/dynsmf/ui-model.smf`, and its exports list.
No new id-naming scheme, no `X2`/`v1`/`v2` split.

---

## P2 — Cache / invalidation hardening

- **Staleness = content hash, not mtime** — already implemented (`.srchash` +
  `rt_hash_text`, `dynsmf_session.spl:165-193`). Keep it. Add a test that a whitespace-only
  edit that changes bytes invalidates, and that a touch-without-edit does not.
- **On stale/missing:** auto-rebuild via the existing background-compile queue
  (`dynsmf_autoload.spl:17-41`) **or** fall back to source-interpret with a **one-line
  warning** — but note the facade today fails closed (research §1.5); the fallback must live
  in the caller and be tested. `--dynsmf-status` must show the fallback, not hide it.
- **Cache location:** `build/dynsmf/<id>.smf` (arch doc §"dynSMF Manifest Registry"). Does
  not exist in this checkout — creating it is part of the first rollout, not assumed.
- **Build integration + documented cost:** wire the 7 (+1) build plans into `bin/simple
  build` (today they are NOT — research §1.4). **Document the measured per-module build
  time** the first time artifacts are produced (currently the 120 s/module figure in
  `check-low-dependency-dynsmf-build-plans.shs` is a timeout ceiling, not a measurement).
  The build uses `bin/simple compile` = the native-build frontend (~0.8 ms/char); expect
  large per-module cost and record it — it is the ROI denominator (research §3).

---

## P3 — Gaps / blockers to file as concrete records (do NOT fix here)

1. **Execution-wiring gap** — `smf_dlopen*`/`smf_dlsym` never call `ModuleLoader::load`;
   dynSMF loads execute no code (research §1.2). File as a feature request:
   "Wire dynSMF facade to native ModuleLoader (real symbol resolution + call-through)."
   This is P0 Gate 1's implementation and is the single largest blocker.
2. **Manifest schema has no variant/platform field** (`DynSmfManifestEntry`,
   `dynsmf_session.spl:8-16`) — cannot express per-platform GPU backends or variant
   families. File as a feature request before any 2d/gui widening.
3. **`gui_renderer` id/content mismatch** — id maps to a web backend file, not a GUI module
   (research §1.3). File as a bug; resolve before proposing a real GUI id.
4. **Independent web-engine blockers** — quadratic 336 KB-CSS hang + self-hosted parser
   gaps (`mut` params, destructuring) (project memory). Reference the existing records; do
   not duplicate. These gate any `web_renderer` widening independent of dynSMF.
5. **Graphics `SIMPLE_EXECUTION_MODE=interpret` constraint** — unhandled by the facade
   (research §4). File as a blocker for any real GUI id.

---

## Non-goals (explicit)

- **No Rust-seed changes.** All fixes in pure-Simple + packaging; builds shell to
  `bin/simple compile` (self-hosted release), never the seed.
- **No bypassing `SIMPLE_EXECUTION_MODE=interpret` for graphics** until proven safe.
- **No new module-id naming schemes** — no `X2`/`v1`/`v2` splits; widen coverage by editing
  the existing manifest entry's source or adding one clearly-named id.
- **No breaking app→facade isolation** — apps call only facades; the dependency-gate
  forbidden-prefix rules stay enforced.
- **No silent violation of arch-doc exclusions** — parts the arch doc excludes stay
  excluded; propose an arch change separately.

---

## Impl recipe for a sonnet agent (per P1 module id — ONLY after P0 both-green)

**Do nothing while P0 is red.** When P0 passes, per id in P1 order:

1. **Files to touch:**
   - `src/os/smf/dynsmf_session.spl` — set `default_autoload` on the target entry (or add
     one `DynSmfManifestEntry` for `ui-model`). Index-`while` iteration only.
   - `build/dynsmf/<id>.smf` — produced by `bin/simple compile <source> -o
     build/dynsmf/<id>.smf`; commit the build-plan wiring, not the artifact (do not add
     artifacts to git).
2. **Default-flip mechanism:** the autoload policy table (`dynsmf_default_manifest`) is the
   only switch. No caller edits beyond the fallback-warning path (P2).
3. **Tests to run (all must be green):**
   - `bin/simple test test/01_unit/os/smf/dynsmf_session_spec.spl`
   - `bin/simple test test/01_unit/os/smf/smf_dynlib_spec.spl`
   - `bin/simple test test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl`
   - `bin/simple test test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl`
   - `bin/simple test test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl`
   - the stale-artifact correctness test (P0).
4. **Perf measurement protocol:**
   - 3-run median, both before (interpret-source) and after (SMF default-on), on the id's
     representative lane (small UI spec for `ui-model`/`render2d`; a TUI cold run for
     `tui_renderer`).
   - **Target-lane threshold:** improvement must be **≥ 0.30 s AND ≥ 10 %** of the lane
     baseline (P0 Gate 2). Below that → revert the flip and confirm NO-GO for that id.
   - **Non-target guard:** every other lane in the baseline table must stay within **±10 %**
     wall of its baseline. A regression outside ±10 % on any non-target lane reverts the flip.
   - Verify **no new FFI hop / no extra pixel copy** (grep for added `rt_*`; check the
     `WebRenderPixelArtifactCache` hit-rate is unchanged — see backend-isolation plan's perf
     anchors).

---

## Verdict

**NO-GO** — see research §6. This plan is the re-open procedure: pass P0 Gate 1
(execution-wiring) and Gate 2 (≥0.30 s AND ≥10 % measured win) before any P1 flip. Absent
those, defaulting more lib parts to SMF adds bookkeeping and stale-artifact risk with zero
functional or measured perf benefit.
