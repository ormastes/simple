# Research: Default-on precompiled+cached SMF for tui/ui/gui/web/2d lib parts

**Purpose:** Decide, with numbers, whether making many tui/ui/gui/web/2d library
parts default to precompiled + cached (dyn)SMF modules is a perf win, how big,
and what a safe rollout would be. The premise under test: interpreted re-parse is
the bottleneck (folklore figure ~0.8 ms/char linear), and SMF-loading a module
skips parse for that module entirely.

**Status:** Analysis — **NO-GO** under current infrastructure (see verdict).
**Last Updated:** 2026-07-06
**Reads-with (plan):** [`doc/03_plan/ui/perf/smf_default_ui_caching_plan.md`](../../../03_plan/ui/perf/smf_default_ui_caching_plan.md)

---

## 1. Current state (from infra map)

Full evidence with file:line citations: scratchpad `smf_infra_map.md`. Load-bearing
findings:

1. **A dynSMF scaffold already exists and is default-on.** Manifest
   `dynsmf_default_manifest` (`src/os/smf/dynsmf_session.spl:69-78`) declares 7 ids —
   `file_io`, `net_io`, `render2d`, `web_renderer`, `gui_renderer`, `tui_renderer`,
   `ui_html` — **all `default_autoload=true`**. Startup wires them via
   `src/app/startup/dynsmf_autoload.spl` with policy flags `--no-dynsmf`,
   `--disable-dynsmf=<ids>`, `SIMPLE_DYNSMF=0`, `SIMPLE_DYNSMF_DISABLE=<ids>`.

2. **The load path executes no code.** `smf_dlopen`
   (`src/os/smf/smf_dynlib.spl:148-161`) returns a synthetic incrementing handle —
   no dlopen/mmap. `smf_dlopen_checked` (`:166-182`) adds only file-exists + first-4-bytes
   `SMF\0` magic. `smf_dlsym` (`:184-205`) reads a **text-encoded** `"handle:sym:offset;…"`
   registry string built from the manifest's static `exports` order
   (`dynsmf_session.spl:316-322`), not a real symbol table. **Nothing calls the real
   native `ModuleLoader::load`** (`src/compiler_rust/runtime/src/loader/loader.rs:16-36`)
   and nothing jumps into a loaded artifact's code section. A dynSMF "load" is
   bookkeeping/evidence only.

3. **Coverage of the five target lib parts is thin** (opportunity table below):
   - **tui**: `tui_renderer` maps to an 8-line shim (`src/app/ui.render/tui_widgets.spl`),
     not the real backend closure (`app.ui.tui/backend.spl`, `screen.spl`, `input.spl`).
   - **ui (common model/layout/style)**: `src/lib/common/ui/*` (40+ files) is **not covered**
     except a 28-line `html_ui/dynsmf_entry.spl`.
   - **gui**: `gui_renderer` actually points at a *web* backend (`src/app/ui.web/backend.spl`),
     not any native GUI/WM file — naming/content mismatch, no real GUI covered.
   - **web**: `web_renderer`/`ui_html` cover only the HTML *widget* layer, not the real
     parse→layout→paint engine (`app.ui.browser/backend.spl`, `css.spl`).
   - **2d**: `render2d` covers only a 208-line lane-selection contract
     (`backend_lane.spl`), not the ~30 GPU backend files.

4. **No artifacts have ever been built here.** `build/dynsmf/` does not exist; per-module
   build time is unmeasured. Building is `bin/simple compile <src> -o <out>` (NOT part of
   `bin/simple build`); the only triggers are opportunistic async background compile at
   startup (`dynsmf_autoload.spl:17-41`) and a manual check script with a **120 s/module
   timeout ceiling** (`scripts/check/check-low-dependency-dynsmf-build-plans.shs`).

5. **Staleness is content-hash** (`.srchash` sidecar via `rt_hash_text`,
   `dynsmf_session.spl:165-193`), not mtime. Foreground autoload **fails closed**: a
   missing/stale/invalid artifact yields `"failed"`/`"artifact_<reason>"` evidence and the
   library is simply not loaded — no in-facade fallback-to-interpret.

6. **Interp module cache is per-process only** (`_interp_module_fast_cache`/`_interp_module_cache`
   in `module_loader_resolve.spl:29-30`) — in-memory maps, no disk serialization. Every fresh
   `bin/simple run/test/compile` reparses/re-resolves from scratch. This is the parse surface
   SMF would target.

---

## 2. Baseline numbers (from perf baseline)

Median of 3 runs, macOS arm64, `SIMPLE_EXECUTION_MODE=interpret` where noted
(scratchpad `smf_perf_baseline.md`):

| Lane | Command | Median | Composition |
|---|---|---|---|
| Browser snapshot | `SIMPLE_EXECUTION_MODE=interpret sh scripts/check/check-macos-metal-browser-backing-evidence.shs` | **6.478 s** | Full pixel-capture across 3 subprocess renderers (Simple Metal + Chrome + Electron) |
| Small UI spec | `bin/simple test .../engine2d/backend_order_spec.spl` | **0.457 s** | Parse+resolve+interp of a 3554-byte spec + engine2d closure (1480 KB) |
| CLI cold run | `bin/simple run examples/01_language/hello.spl` | **0.125 s** | Process start + parse + interp of a trivial file |
| Browser closure size | `grep` direct imports of `ui.browser/main.spl` | **3396 KB** | browser_engine 1916 KB + engine2d 1480 KB; 5 direct imports |
| Phase profile | `SIMPLE_COMPILER_PHASE_PROFILE=1` on the spec | — | No `BOOTSTRAP-PHASE` lines (this is the interpret-run path, not native-build) |
| `--dynsmf-status` | flag on `ui.browser/main.spl` | — | Flag not available on this binary |

---

## 3. Win model — and why it collapses against the one measured point

**Premise:** time saved per lane ≈ (parsed bytes avoided) × 0.8 ms/char.

**Validation against a measured point (falsifies the premise for the run lane):**

- Browser closure = 3396 KB = 3,477,504 bytes. Premise predicts parse cost
  ≈ 3,477,504 × 0.8 ms = **2782 s ≈ 46 min**.
- Measured browser snapshot lane = **6.478 s total**, and that total is dominated by
  three subprocess renderers, not by Simple parse.
- 46 min predicted vs 6.478 s measured is a **~430× contradiction**. The 0.8 ms/char
  figure is therefore **not** the interpret-run parse cost. Per project memory it is the
  **native-build frontend** cost (`native-build → cli_run_file`, ~0.8 ms/char, "90 min
  for main.spl closure" — the Stage-4 deploy blocker). That is the compiler frontend run
  *interpreted* during `bin/simple compile` — i.e. **the exact path that BUILDS an SMF**,
  not the path that a normal `bin/simple run` uses.

**Actual interpret-run per-char cost (derived, upper bound):**
`(0.457 s − 0.125 s) / 1,515,520 bytes` (engine2d closure delta) ≈ **0.22 µs/char**, and that
delta bundles resolve + interpretation, so parse *alone* is a fraction of 0.22 µs/char —
roughly **3600× cheaper** than the 0.8 ms/char premise.

**Predicted parse-avoidance win per lane (upper bound, using ≤0.22 µs/char on the whole
closure):**

| Lane | Closure parsed | Upper-bound win if parse fully skipped | Reality |
|---|---|---|---|
| Browser snapshot | 3396 KB | ≤ ~0.76 s | Lane is subprocess-pixel bound; parse is a small slice of 6.478 s → realistic win **< 0.3 s**, and SMF cannot touch subprocess time |
| Small UI spec | ~1480 KB (engine2d) | ≤ ~0.33 s (whole parse+resolve+interp delta) | Parse-only fraction **≪ 0.33 s**; spec total is 0.457 s |
| CLI cold TUI run | trivial | ≤ ~0.02 s | Parse cost negligible in the 0.125 s |

**The economics invert.** Building an SMF pays the **0.8 ms/char native-build** frontend
(~46-min-class for the browser closure; smaller per leaf module but real and, in this
checkout, never once completed) to save a run-time parse worth **≤ 0.3 s**. Content-hash
staleness forces a rebuild on **every edit** to the module or anything in its closure.
Break-even requires on the order of **thousands of runs between edits** — implausible for
UI libraries under active development.

---

## 4. Risk register

| Risk | Evidence | Severity |
|---|---|---|
| **Execution gap** — dynSMF load runs no code | `smf_dlopen*`/`smf_dlsym` validate magic + read a text registry only; no call into `ModuleLoader::load` (`smf_dynlib.spl:148-205`) | **Blocker** — functional win today is 0; flipping more ids on adds evidence, not behavior |
| **Win model falsified** — 0.8 ms/char is the build path, not the run path | §3; 46 min predicted vs 6.478 s measured | **High** — removes the perf premise entirely for the run lane |
| **Negative build ROI** — precompile pays the slow native-build frontend | `bin/simple compile` = native-build frontend (0.8 ms/char); staleness = per-edit content hash (`dynsmf_session.spl:181-193`) | **High** |
| **Stale-artifact correctness on shared UI** — caching `common/ui/*` means one staleness bug silently corrupts every TUI/web/GUI surface at once | `common/ui/*` is the shared contract layer for all backends (arch doc §"Common UI Contracts") | **High** |
| **Cranelift struct-array codegen bug** — forced index-loops before | `[DynSmfManifestEntry]` etc. already avoid `for x in [Struct]` (index-`while` only, `dynsmf_session.spl`); any new table-driven code must too | Medium — mitigated but a live landmine |
| **Graphics `SIMPLE_EXECUTION_MODE=interpret` constraint** — winit/graphics JIT panics without it | No `SIMPLE_EXECUTION_MODE` read/set anywhere in `src/os/smf` or `dynsmf_autoload.spl`; moot only because nothing executes yet | High for any real GUI id |
| **Variant dirs** — `DynSmfManifestEntry` has no variant/family/platform field | `dynsmf_session.spl:8-16`; manifest already spans `nogc_sync_mut`/`gc_async_mut`/`common` with one hard-coded path per id | Medium — cannot express per-platform GPU backends without schema change |
| **Bootstrap purity** — must keep shelling to `bin/simple compile` (self-hosted release), never the seed | background spawn + check script both use `bin/simple compile` (consistent) | Low — already satisfied |
| **App→facade isolation** — must not let TUI closure transitively reach web/HTML/CSS | dependency-gate spec enforces import-boundary strings (`low_dependency_ui_dynsmf_dependency_gate_spec.spl:87-92`) | Medium — widening `web_renderer`/`gui_renderer` to real engines risks pulling HTML/CSS into TUI paths |
| **Independent web/gui blockers** | quadratic 336 KB-CSS hang, self-hosted parser gaps (`mut` params, destructuring), Metal interpret requirement (project memory) | High for web/gui lanes specifically |

---

## 5. Opportunity table + per-part GO/NO-GO

| Lib part | Covered today | Default? | Build cost | Parse-avoid win (validated) | Risk | Per-part verdict |
|---|---|---|---|---|---|---|
| **tui** (real: `app.ui.tui/backend.spl`, `screen.spl`, `input.spl`) | Nominal — 8-line shim only | on (for shim) | Unmeasured; leaf module small | ≤0.02 s (trivial closure) | Low–med (gate boundary) | **NO-GO** — win below noise; shim carries no real parse surface |
| **ui-model/layout/style** (`common/ui/*`, 40+ files) | **No** (28-line entry only) | n/a | Unmeasured; largest shared surface | Largest *potential*, but still ≤ fractions of a second at 0.22 µs/char | **High** (shared → one stale bug corrupts every surface) | **NO-GO now** — highest-value target IF the execution gap closes and a real measurement shows a win; not before |
| **gui** (native WM: `hosted_entry.spl`, winit/Metal) | **No** (id points at a web file) | on (wrong module) | Unmeasured | 0 today | **High** (interpret-mode constraint + no code exec = fake evidence risk) | **NO-GO** — would repeat the "no fake GUI evidence" mistake in project memory |
| **web / browser_engine** (`browser/backend.spl`, `css.spl`) | Partial (HTML widget layer) | on (widget layer) | Unmeasured; largest closure (1916 KB) | Bounded < 0.3 s; lane is subprocess-bound | **High** (quadratic CSS hang, parser gaps, HTML/CSS-into-TUI leak) | **NO-GO** — strongest a-priori parse case yet still blocked by independent unresolved issues |
| **2d / engine2d** (GPU backends, ~30 files) | Partial (208-line lane contract) | on (contract file) | Unmeasured | ≤0.33 s upper bound (whole delta, not parse-only) | Medium (no platform field for per-backend selection) | **NO-GO** — backends mutually exclusive at runtime; manifest can't express per-platform selection |

---

## 6. Verdict

**NO-GO** at current infrastructure maturity, for four independent reasons, any one of
which is sufficient:

1. **Functional:** the dynSMF load path executes no loaded code (§1.2). Flipping ids to
   default-on changes evidence, not behavior. Win today = 0.
2. **Perf premise falsified:** the 0.8 ms/char figure is the native-build frontend cost
   (the *build* path), not the interpret-run parse cost. Validated against the browser lane
   (46 min predicted vs 6.478 s measured, §3). Real run-lane parse cost is ≤0.22 µs/char.
3. **Negative ROI:** precompiling pays the ~46-min-class native-build frontend to save
   ≤0.3 s of run parse, with per-edit content-hash rebuilds. Break-even needs thousands of
   runs per edit.
4. **Correctness:** the only large shared parse surface (`common/ui/*`) is exactly the one
   whose staleness bug would silently corrupt every UI backend at once.

**A NO-GO with numbers is the deliverable.** The plan document specifies the two gates that
would have to pass before any future GO (execution-wiring proof + a real, measured
parse-avoidance win on a representative lane), so the decision is re-openable on evidence,
not on folklore.
