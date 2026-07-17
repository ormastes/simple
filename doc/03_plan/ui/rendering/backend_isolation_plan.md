# Backend-Isolation Plan — App → Facade → Engine2D → Backend → `rt_*`

## Owner review update (2026-07-17)

Nineteen newly detected `examples/09_embedded/simple_os/arch/**` entry and
probe files are exact bare-metal implementation owners: they exercise hardware,
QEMU exit, target runtime ABI, or target-only services from restricted entry
closures. Their exact paths are ratchet-baselined with an annotated provenance
block; no directory wildcard is used, so every future file still fails closed.
Hosted app consumers remain violations and are not absorbed by this review.

Three additional exact owners remain ratcheted pending dedicated prerequisites:
the contract-pinned minimal freestanding argv facade, the SimpleOS guest target
pipeline, and the WM Draw IR scalar-buffer workaround for documented Stage3
aggregate corruption and QEMU FFI cost. Their existing contract tests pin the
restricted closures; the hosted image patcher and CLI test entry remain
unclassified consumer violations, and the SimpleOS tool main remains a facade
migration item.

**Status:** GATE LIVE, GAPS OPEN (2026-07-07) · **Owner:** UI/rendering · **Scope:** enforce the
three-facade rendering architecture across `src/app/**` and `examples/**`.

## Current state (verified 2026-07-07)

**Gate is live and wired.** `scripts/check/check-ui-backend-isolation.shs` (134 lines) greps for
(a) `\brt_[a-z0-9_]+` extern/call tokens and (b) direct
`MetalBackend|VulkanBackend|DirectXBackend|SoftwareBackend(` construction, over
`src/app examples src/lib/*/ui`, excluding `**/vendor/**`, `**/node_modules/**`,
`src/app/interpreter/ffi/**`, `src/lib/nogc_sync_mut/ui/**`, ratcheted against
`scripts/check/ui_backend_isolation_baseline.txt`. Live gate output:

```
ui_backend_isolation_baseline_stale=RT:src/app/ui.browser/backend.spl
ui_backend_isolation_baselined=537
ui_backend_isolation_current=536
ui_backend_isolation_new=0
ui_backend_isolation_ok=true
```

- **Baseline 537, current 536, new 0** — burn-down is monotone; one baseline entry
  (`RT:src/app/ui.browser/backend.spl`) is **stale** (no longer reproduces) → first ratchet target.
- **Wiring: both places.** Pre-commit hook `scripts/hooks/pre-commit:19`
  (`sh scripts/check/check-ui-backend-isolation.shs`); lint aggregator
  `src/app/io/_CliCommands/run_commands.spl:218` inside `cli_run_lint` (folds `iso_exit` into
  the overall exit code).
- **Known inert lane (bug record).**
  `doc/08_tracking/bug/build_lint_routes_to_rust_clippy_not_cli_run_lint_2026-07-06.md`:
  `bin/simple build lint` routes to Rust-driver clippy (`misc_commands.rs:126,181` → `cargo
  clippy`), so pure-Simple `cli_run_lint` never runs — **the isolation gate is inert on the
  `build lint` lane**. It runs correctly via pre-commit and any direct `cli_run_lint` invocation.
  Until that bug is fixed, do not rely on `build lint` to enforce this gate; the pre-commit hook is
  the load-bearing path. (This is a wiring bug to fix, not a reason to duplicate the gate.)

**Gaps B–F re-verified present (2026-07-07)** — anchors refreshed against source:
- Gap B: `web_render_backend(` defined `web_render_backend.spl:222`, **zero callers** in
  `src/app`/`src/os`; no `--web-engine` flag in `src/app/ui.browser`; `BrowserBackend`
  (`ui.browser/backend.spl`) hardcodes `WEB_RENDER_TARGET_PURE_SIMPLE` at ~11 sites
  (`:34,361,440,514,618,632,649,653,656,665,1075`).
- Gap C: `render_html_to_pixels` (`web_render_backend.spl:164`) still passes `"auto"` at `:167`;
  no `engine2d_backend` param.
- Gap D: `WatchdogManager` **does not exist** anywhere in `src/`;
  `src/app/interpreter/core/watchdog.spl` still declares `extern rt_watchdog_start`/`_stop`
  (`:19,:20`, called `:31,:35`).
- Gap E: `WebRenderBackend` (`web_render_backend.spl:152`) exposes only pixel methods —
  `create:158`, `name:161`, `render_html_to_pixels:164`, `render_html_file_to_pixels:169`,
  `show_live_window:177`; no `render_html_to_draw_ir`/software method.
- Gap F seams present: `Engine2D.create_with_backend_fast` (`engine.spl:156`);
  `MetalBackend.use_gpu_only` (`backend_metal.spl:588`, called from `engine.spl:179` — **note:
  the "Perf invariant" section below cites `:492`; the verified line is `:588`**);
  `simd_fill_row` → runtime extern `rt_simd_fill_row_u32` (`simd.rs:1427`);
  `WebRenderPixelArtifactCache` (`web_render_pixel_backend.spl:111`, used `ui.browser/backend.spl:337`).

## Baseline-shrink ratchet plan

The gate ratchets down, never up. Order of shrinks:
1. **Remove the stale entry** `RT:src/app/ui.browser/backend.spl` from
   `scripts/check/ui_backend_isolation_baseline.txt` (537 → the current 536 becomes the new
   ceiling). Do this first — it is free and proves the ratchet.
2. **Each P1/P3 wave** re-runs the gate and lowers the baseline to the new `current`; a wave may
   never raise it. `new=0` must hold on every commit (pre-commit enforces).
3. **Fix the `build lint` clippy-routing bug** (record above) so the gate is enforced on that lane
   too; until then keep the pre-commit path authoritative.
4. **Final target `= 0`** once P3 gaps A–F land and every `src/app/**`/`examples/**` site routes
   through a facade.

**Reads-with:**
- Architecture: [`doc/04_architecture/ui/rendering/backend_isolation_architecture.md`](../../../04_architecture/ui/rendering/backend_isolation_architecture.md)
- Design: [`doc/05_design/ui/rendering/draw_ir_multibackend_design.md`](../../../05_design/ui/rendering/draw_ir_multibackend_design.md) § "Layering: app-level backend isolation (2026-07-06)"
- Dev guide: [`doc/07_guide/ui/rendering/backend_isolation_guide.md`](../../../07_guide/ui/rendering/backend_isolation_guide.md)
- Sibling plan (Engine2D internals): [`draw_ir_multibackend_plan.md`](draw_ir_multibackend_plan.md)

**Running dependencies (do not duplicate their work here):**
- Task #20 — **D2 Engine2D consolidation** (design § "Decisions (2026-07-06): D1, D2, D4
  APPROVED_WITH_CHANGE"): collapses the dead 3-way `Engine2D` branch and the two disagreeing
  backend-selection paths onto one. The facade recipe below assumes the *single* consolidated
  `create_requested_backend` selector; do not re-wire selection here.
- Task #15 — **WM wiring** (native `GuiRenderer` core through
  `os.compositor.host_compositor_entry` / `os/hosted/hosted_entry.spl`): P3 Gap A depends on this
  landing so the electron/native cases have a real `CompositorBackend` to route to.

---

## The architecture being enforced (3 facades, one shape)

| Facade | Pluggable engines | App-visible API | Backend chosen by |
|---|---|---|---|
| **Simple2D** (`Engine2D`) | metal · vulkan · directx · software · cpu_simd (+ cuda/rocm/opencl/opengl/webgpu…) | `Engine2D.create_requested_backend(w,h,name)` → `RenderBackend`/`Engine2DExtended` | NAME string |
| **WebRenderer** (`WebRenderBackend`) | `chromium` · `pure_simple` (native layout/paint via Engine2D) | `web_render_backend(name,w,h).render_html_to_pixels(html)` | NAME string |
| **GuiRenderer** (does not exist yet — P3 Gap A) | `electron` · `gui_renderer_core` (WM/hosted_entry) | `GuiRenderer.create(name,…)` → window/session/present | NAME string |

**Isolation rule.** Apps, examples, and UI libraries call **only facades**. A facade may call
Simple2D. Only backend implementations (`src/lib/*/gpu/**` and the designated `ffi`/`io` modules)
may **declare or call** `rt_*` externs. An `extern rt_*` declaration or an unwrapped backend-engine
call in `src/app/**` (except `src/app/interpreter/ffi`, per allowlist below) is a **violation**.

**Perf invariant (non-negotiable).** A facade adds **no per-call FFI hop and no extra
pixel-buffer copy**. The following seams are non-regression anchors — the fix wave must route
*through* them, never around them:
- Metal no-mirror fast path: `Engine2D.create_with_backend_fast` (`engine.spl:156`) →
  `MetalBackend.use_gpu_only()` (`backend_metal.spl:492`). A facade must not downgrade the metal
  case to `create_with_backend`.
- Batched Metal buffer FFI: `rt_metal_buffer_upload`/`_download`/`rt_metal_set_bytes`
  (`backend_metal_runtime_ops.spl:2-4`) — one shot per frame, no per-primitive marshalling.
- NEON/SSE2 row kernels: `simd_fill_row` (`nogc_async_mut/gpu/engine2d/simd_kernels.spl:11`) →
  `fill_row_neon`/`copy_row_neon` (`engine2d_simd_ops.rs:95,161`). Never inline row fills in a facade.
- Browser render cache: `WebRenderPixelArtifactCache` (`web_render_pixel_backend.spl:111`) →
  `SimpleWebEngine2DStaticPixelCache.pixels_for_html` (`simple_web_engine2d_renderer.spl:66`).
  `BrowserBackend.render_frame` must keep calling the cache first (`backend.spl:561`).

---

## P0 — Inventory summary (baseline, 2026-07-06)

Source: scout inventory scan. Numbers are the starting baseline the gate (P2) drives to zero.

### Import table (violation classes → forbidden extern/call → target facade)

| Class | Forbidden symbol(s) in `src/app/**` | Files · count | Target facade | Facade exists? |
|---|---|---|---|---|
| **A. Window/event FFI** | `extern rt_winit_*` (11), `rt_winit_*` calls (18+) | `ui.browser/app.spl` | **GuiRenderer** | ❌ → P3 Gap A |
| **B. Timing FFI** | `extern rt_time_now_unix_micros` | `ui.browser/app.spl:27`, `ui.browser/backend.spl:27` | `std.nogc_sync_mut.src.time.now_micros` / `io_runtime.time_now_unix_micros` | ✅ → **P1** |
| **C. Watchdog FFI** | `extern rt_watchdog_start/stop` (2) + calls (2) | `interpreter/core/watchdog.spl:19-35` | **WatchdogManager** | ❌ → P3 Gap D |
| **D. Web pixel render** | `simple_web_engine2d_render_html_pixels` (10×), `simple_web_render_html_to_pixels_with_engine2d_backend` (2×) | `office/gui.spl`, `office/gui_apps.spl`, `office/md_wysiwyg_gui.spl`, `office/md_wysiwyg_ppm.spl` | `web_render_backend(...).render_html_to_pixels` | ✅ → **P1** (caveat P3 Gap C) |
| **E. Web capture/probe** | `simple_web_layout_render_html_pixels`, `…_draw_ir`, `…_software_pixels`, `simple_web_engine2d_render_html_readback` | `wm_compare/**` (14 files, 40+), `test/*_capture.spl` (5) | relocate to `gpu/**` test layer, or `web_render_backend` (pixels only) | partial → **P1 (pixels)** + P3 Gap E (draw_ir/software) |

### Counts

| Category | Count | Status |
|---|---|---|
| Files with HIGH `rt_*` violations | 3 | ⚠️ |
| `rt_*` extern decls in app layer | 11 + (2 rt_time) + (2 rt_watchdog) | CRITICAL |
| `rt_*` calls in app layer | 18+ (winit) + rt_time + rt_watchdog | CRITICAL |
| Files with MEDIUM backend-engine calls | 17+ | ⚠️ |
| Backend-engine calls in app layer | 40+ | HIGH |
| Direct backend-class construction (`MetalBackend(…)` etc.) | **0** | ✅ GREEN |

**P0 acceptance:** this table is committed as the baseline; the gate script (P2) reproduces these
counts on `main` and every subsequent count must be ≤ baseline (monotonic burn-down).

---

## P1 — Fix-wave routing recipe (mechanical; real facades only)

Each class below names a **real, existing** facade function (verified against source). A sonnet fix
agent applies these by rote. Classes whose target facade does **not** exist are in P3, not here.

### Class B — timing FFI → `std` time facade  *(2 sites)*

Real facades: `time_now_unix_micros()` (`io_runtime.spl:186`, `pub`), `now_micros()`
(`nogc_sync_mut/src/time.spl:16`, `pub`).

```simple
# BEFORE  (src/app/ui.browser/app.spl, backend.spl)
extern fn rt_time_now_unix_micros() -> i64
...
val t = rt_time_now_unix_micros()

# AFTER
use std.nogc_sync_mut.io_runtime.{time_now_unix_micros}
...
val t = time_now_unix_micros()
```

Delete the `extern` line entirely. No behavior change (facade forwards to the same `rt_*`).

### Class D — web pixel render → `WebRenderBackend`  *(12 sites, office/*)*

Real facade: `web_render_backend(name, w, h)` (`web_render_backend.spl:222`) →
`.render_html_to_pixels(html)` (`:164`). `name` = `"pure_simple"` (Engine2D core) or `"chromium"`.

```simple
# BEFORE  (src/app/office/gui.spl)
use std.gc_async_mut.gpu.browser_engine.simple_web_engine2d_renderer.{simple_web_engine2d_render_html_pixels}
...
val pixels = simple_web_engine2d_render_html_pixels(html, w, h)

# AFTER
use std.gc_async_mut.gpu.browser_engine.web_render_backend.{web_render_backend}
...
val pixels = web_render_backend("pure_simple", w, h).render_html_to_pixels(html)
```

**Two behavior notes the fix agent must record on each converted site:**
1. `render_html_to_pixels` routes the `pure_simple` path through the **real** layout/paint pipeline
   (`simple_web_render_html_to_pixels_with_engine2d_backend`, `simple_web_renderer.spl:86`), **not**
   the `SimpleWebHeuristicSurface` micro-fast-path that `simple_web_engine2d_render_html_pixels`
   uses (`simple_web_engine2d_renderer.spl:808`). Verify parity on each office screen; if a screen
   regressed on the heuristic surface, file against **P3 Gap E**, do not revert the isolation fix.
2. The facade hardcodes the Engine2D backend to `"auto"` (`web_render_backend.spl:167`). Sites that
   passed an explicit backend (`md_wysiwyg_gui.spl:63` passes `"cpu_simd"`) **cannot** be fully
   migrated yet — see **P3 Gap C**. Migrate only the `"auto"`-equivalent sites in this wave.

### Class E-pixels — parity/capture pixel render → `WebRenderBackend`  *(subset of wm_compare/test)*

For sites calling `simple_web_layout_render_html_pixels`/`…_readback` **for a full-page pixel
buffer**, apply the Class D pattern. For sites calling `…_draw_ir` or `…_software_pixels` (no facade
method), **do not** rewrite — route them via P3 Gap E (relocate to `gpu/**` test layer, where
backend-engine access is legitimate for test-tier code).

### P1 acceptance criteria
- Every Class B/D/E-pixels site compiles and its owning spec/parity harness is **green**.
- Perf non-regression: representative render (`bin/simple office --render` and the browser parity
  harness) within **±10 % wall** of the pre-change baseline; `WebRenderPixelArtifactCache`
  hit-rate unchanged; no new FFI hop introduced (verify by grep — no `rt_*` added anywhere).
- Gate (P2) count for classes B, D drops to **0**; class E drops by the pixel-only subset.

---

## P2 — Enforcement gate

**Script (new):** `scripts/check/check-backend-isolation-source-contract.shs` — modeled on
`scripts/check/check-shared-wm-renderer-unification-evidence.shs` (the one source-contract gate).
Reuse from that template:
- Self-hosted-binary discovery + rust-seed-forbidden guard (its lines 12-51) — tooling runs on
  `bin/release/<triple>/simple`, never `src/compiler_rust/*`.
- `set +e` capture around `check` + `test --mode=interpreter --clean --format json`, parsing
  `total_passed`/`total_failed` (its lines 96-116).
- Source-contract grep block (its lines 118-125) — here it asserts **absence**: no `extern rt_`
  and no backend-engine symbol in `src/app/**` outside the allowlist.
- `key=value` stdout + markdown evidence to `doc/09_report/`, nonzero exit on any violation.

**Allowlist (exact dirs where `rt_*` / backend-engine calls are legitimate):**
```
src/lib/**/gpu/**            # backend implementations + Engine2D
src/lib/**/io/**             # io/timing/net facades that own rt_* wrappers
src/lib/nogc_sync_mut/**     # sync-mutable ffi/fs/net facades
src/app/interpreter/ffi/**   # interpreter runtime FFI (rt_ast_*, rt_env_*, rt_error_*)
src/os/compositor/**         # native GUI core (CompositorBackend)
src/os/hosted/**             # hosted_entry native GUI core
```
Everything else under `src/app/**` and all of `examples/**` is **forbidden** to declare/call `rt_*`
or the `simple_web_*` backend-engine functions directly.

**Lint wiring:** register the script in the check aggregator so `bin/simple build check` runs it;
add it to the pre-commit hook list alongside `check-workspace-root-guard.shs`. Emit machine-readable
`backend_isolation_violations=<n>` so CI can gate.

**P2 acceptance:** gate reproduces the P0 baseline on `main`; after each P1 wave the reported count
is strictly ≤ prior; final target `backend_isolation_violations=0` once P3 gaps land.

**Follow-up — scan-root coverage gap (found 2026-07-07, GPU-dict pilot W1).** The live gate
`scripts/check/check-ui-backend-isolation.shs` scans only `src/app examples src/lib/*/ui`, so
`src/lib/**/gpu/engine2d/**` — where backend implementations legitimately hold `rt_*` — is **not
scanned at all**. That is correct for *forbidding* app-side leakage, but it means the gate cannot
assert the **positive** backend-side property the pilot relies on: that a new GPU-dict op stays
**upload-only** (no *new* `extern rt_*` beyond the allowlisted buffer-upload/dispatch surface). W1's
upload-only property was therefore **hand-verified this pass**, not machine-checked. Follow-up: add
an allowlist-delta check over `src/lib/**/gpu/**` (assert the `extern rt_*` set is a subset of a
pinned baseline, so a future GPU-dict op adding a *new* extern trips a gate) — cheaper than
widening the forbidding scan, and closes the exact gap the pilot walked around. (Independent note:
the current gate reports `new=5` on 2026-07-07, all from origin `src/app/llm_caret/**` and
`examples/09_embedded/simple_os/**` — **zero from W1**, precisely because W1 lives in the unscanned
`gpu/engine2d` dir. Baseline refresh for those 5 is the owning authors' item, not W1's.)

---

## P3 — Facade gaps to build (no API may be invented in the P1 recipe until these land)

### Gap A — **GuiRenderer facade does not exist** (blocks Class A: `rt_winit_*`)
No `GuiRenderer` class in `src/`. `HostBackendKind.Electron` (`host_compositor_entry.spl:37`) is a
dead enum variant — `_create_backend_for_kind` (`:494-512`) has no `Electron` case and falls through
to `HeadlessHostCompositorBackend`. **Build** a `GuiRenderer.create(name, …)` wrapper mirroring
`WebRenderBackend`'s shape: `name="gui_renderer_core"` routes to the native
`CompositorBackend`/`os/hosted/hosted_entry.spl` path (Task #15); `name="electron"` shells the
existing `tools/electron-shell` launcher. Do **not** invent a third renderer. Migrate
`ui.browser/app.spl`'s 11 `rt_winit_*` externs + 18 calls onto it. **Depends on Task #15.**

### Gap B — **WebRenderer facade has zero callers** (chrome/core unreachable from apps) — **LANDED (2026-07-07)**
`BrowserBackend.create(w, h, backend, web_engine = "pure_simple")` now threads a `--web-engine`
selector (accepts `--web-engine <name>` and `--web-engine=<name>` in `cli_browser`) through
`web_render_backend(name,w,h)`. Default (`pure_simple`) preserves the `WebRenderPixelArtifactCache`
cache-first path unchanged (byte-identical, perf anchor intact — Gap F). `chromium` renders via the
real `WebRenderBackend` facade and tags the artifact with honest provenance (`compatibility_renderer`
status, `chromium` backend). Unknown engine names loud-fail at construction (`Err`), never silently
default.

**Known caveat — chromium lane is native/compiled-mode only.** Under
`SIMPLE_EXECUTION_MODE=interpret`, the first render call on the chromium lane crashes loudly with
`error[E1002] function 'web_backend_env_get' not found` — a pre-existing interpreter module-alias
resolution gap in `web_render_backend.spl` (`mod_stub -> env_ops` re-export chain), not a Gap B
regression and not a silent fallback. See
`doc/08_tracking/bug/web_backend_env_get_alias_unresolved_interpret_2026-07-07.md`. Pinned by
`test/03_system/gui/ui_browser/backend_isolation_chromium_env_get_gap_b_spec.spl`, which documents
the flip to a real-pixels assertion once the facade bug is fixed.

### Gap C — **`WebRenderBackend` cannot select the Engine2D backend for the core path** — **LANDED (2026-07-08)**
`render_html_to_pixels`/`render_html_file_to_pixels` (`web_render_backend.spl:164,176`) now take an
optional `engine2d_backend: text = "auto"` param plumbed straight into
`simple_web_render_html_to_pixels_with_engine2d_backend`; the default preserves prior behavior
byte-for-byte (pinned by `simple_web_renderer_spec.spl`'s new "backend-isolation Gap C" case —
default vs explicit `"auto"` byte-identical, explicit `"software"` matches
`SimpleWebRenderer.create_with_backend(..., "software")`). Unblocks full migration of
`md_wysiwyg_gui.spl`/`md_wysiwyg_ppm.spl` (Class D note 2) — tracked as the follow-up item below,
not yet migrated.

### Gap D — **WatchdogManager facade does not exist** (blocks Class C: `rt_watchdog_*`) — **LANDED (2026-07-08)**
`WatchdogManager` (`src/lib/nogc_async_mut_noalloc/execution/watchdog_manager.spl`) now owns the
`rt_watchdog_start`/`rt_watchdog_stop` externs and exposes `WatchdogManager.start()/stop()`.
`src/app/interpreter/core/watchdog.spl` is migrated onto it (`start_watchdog`/`stop_watchdog` call
`WatchdogManager.start`/`.stop`; the public app-layer API — `start_watchdog`, `stop_watchdog`,
`check_timeout` — is unchanged). Baseline (`scripts/check/ui_backend_isolation_baseline.txt`) drops
537→536 for this entry. Pinned by the new `watchdog_manager_spec.spl` source-contract spec.

**Caveat — dead-or-dormant, not wired to a real implementation.** `rt_watchdog_start`/`rt_watchdog_stop`
have no native FFI registration anywhere in the Rust runtime, and neither `watchdog.spl`'s API nor
`WatchdogManager` has any caller repo-wide — true before and after this migration (this is a
mechanical isolation-ratchet move with zero behavior change, not a functional fix). See
`doc/08_tracking/bug/watchdog_externs_unregistered_module_uncalled_2026-07-08.md` for the full
finding; owner to decide delete-vs-wire-up. (The Rust driver's own `start_watchdog`/`stop_watchdog`
in `src/compiler_rust/compiler/src/watchdog.rs` is a *different* mechanism, called directly from
Rust, unrelated to these externs.)

### Follow-up — **`office/*.spl` direct-call cleanup** (mechanical, P1-shaped)
Now that Gap C is landed, `WebRenderBackend` can express every call shape the remaining direct
callers need — but `md_wysiwyg_gui.spl`, `md_wysiwyg_ppm.spl`, `gui.spl`, and `gui_apps.spl` (all
under `src/app/office/`) still call `simple_web_render_html_to_pixels_with_engine2d_backend` /
`simple_web_engine2d_render_html_pixels` directly instead of through the facade
(`web_render_backend(...).render_html_to_pixels(html, engine2d_backend)`). This is the remaining
Class D violation set from the P0 inventory (§ Import table) — a mechanical P1-shaped wave, not
blocked by any further facade gap.

### Gap E — **No facade for draw-IR / software-only readback**
`WebRenderBackend` exposes only `render_html_to_pixels`; `wm_compare` probes call
`…_draw_ir`/`…_software_pixels` directly. **Either** add `render_html_to_draw_ir()` and
`render_html_software_pixels()` methods to `WebRenderBackend` (readback with a `ReadbackSource`
provenance tag so parity specs can assert it), **or** relocate the probe files into the
`gpu/**` test layer where backend-engine access is legitimate. Recommended: relocate test-only
harnesses; add methods only for probes that must run from an app entrypoint.

### Gap F — perf non-regression constraint (applies to A–E)
No facade wiring may bypass `create_with_backend_fast` (Metal), the batched Metal buffer FFI, the
NEON/SSE2 row kernels, or the `WebRenderPixelArtifactCache` single-slot memo. Each gap's PR must
cite these four seams as passing non-regression anchors.

### P3 acceptance criteria
- Each gap ships facade + migration + spec, with the perf anchors (Gap F) verified green and within
  ±10 % wall on the representative render.
- After all gaps land, P2 reports `backend_isolation_violations=0` and the browser/office/WM parity
  harnesses are green.
