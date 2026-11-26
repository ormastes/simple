# Bug: wm-lane-boundary ratchet has 7 new uncaught violations
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Found**: 2026-08-08, via `scripts/check/check-wm-lane-boundary.shs` (an
unwired guard under triage in the guard-wiring campaign — currently nothing
runs this gate, so these violations have been silently accumulating).

## Symptom

```
NEW VIOLATION src/app/wm_showcase/session.spl:51:WML001
NEW VIOLATION src/app/wm_showcase/session.spl:61:WML001
NEW VIOLATION src/app/wm_showcase/session.spl:62:WML001
NEW VIOLATION src/app/wm_showcase/session.spl:63:WML001
NEW VIOLATION src/app/wm_showcase/session.spl:64:WML001
NEW VIOLATION src/lib/common/ui/window_scene_draw_ir.spl:196:WML002
NEW VIOLATION src/lib/gc_async_mut/gpu/engine2d/backend_software.spl:40:WML001
FAIL — 7 NEW portable-lane violation(s); 131 total over 501 file(s) scanned
```

Ratchet baseline: `doc/08_tracking/wm_lane_boundary_baseline.txt`.
Scanner: `bin/simple run src/app/check/wm_lane_boundary_check.spl`.

WML001 = use of `fs`/`net`/`process`/`env`/`timers` outside the WM/GUI
portable lane. WML002 = raw platform `extern` outside the lane.

## Impact

These 7 sites have drifted past the recorded ratchet baseline with nothing
catching it — the exact "unwired guard = silent regression" failure mode this
guard-wiring campaign exists to close.

## Next step (owner decision needed)

Either:
1. Fix the 7 sites (`src/app/wm_showcase/session.spl` lines 51/61-64,
   `src/lib/common/ui/window_scene_draw_ir.spl:196`,
   `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl:40`) to stay
   inside the portable-lane contract, or
2. Re-baseline `doc/08_tracking/wm_lane_boundary_baseline.txt` with an
   explicit, reviewed justification for each new entry.

Once resolved, wire `check-wm-lane-boundary.shs` into
`scripts/check/pre-push-conflict-tree-guard.shs` (fast, deterministic, no
hardware deps — it should already have been there per its own header).

## Re-verification 2026-08-17

Ran the actual guard (this repo's default, no build needed — the checker
runs via `bin/simple run`, ~400s wall including the ~310s fixed interpreter
setup cost documented in `.claude/rules/commands.md`):

```
$ sh scripts/check/check-wm-lane-boundary.shs
...
NEW VIOLATION src/app/wm_showcase/session.spl:51:WML001
NEW VIOLATION src/app/wm_showcase/session.spl:61:WML001
NEW VIOLATION src/app/wm_showcase/session.spl:62:WML001
NEW VIOLATION src/app/wm_showcase/session.spl:63:WML001
NEW VIOLATION src/app/wm_showcase/session.spl:64:WML001
NEW VIOLATION src/lib/common/ui/window_scene_draw_ir.spl:202:WML002
NEW VIOLATION src/lib/gc_async_mut/gpu/engine2d/backend_software.spl:40:WML001
NEW VIOLATION src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl:19:WML002
NEW VIOLATION src/lib/gc_async_mut/gpu/engine2d/metal_session.spl:23:WML001
NEW VIOLATION src/os/services/wm/rv64_production_wm_adapter.spl:7:WML001
NEW VIOLATION src/os/services/wm/rv64_production_wm_adapter.spl:8:WML001
NEW VIOLATION src/os/services/wm/rv64_production_wm_producer.spl:7:WML001
NEW VIOLATION src/os/services/wm/rv64_production_wm_producer.spl:8:WML001
NEW VIOLATION src/os/services/wm/rv64_production_wm_producer.spl:9:WML001
NEW VIOLATION src/os/services/wm/rv64_production_wm_producer.spl:10:WML001
NEW VIOLATION src/os/services/wm/rv64_production_wm_producer.spl:11:WML001
NEW VIOLATION src/os/services/wm/wm_codec.spl:65:WML002
FAIL — 11 NEW portable-lane violation(s); 131 total over 515 file(s) scanned
```

**The backlog has grown, not shrunk**: 11 new violations now (was 7 on
2026-08-08), across more files (`rv64_production_wm_adapter.spl`,
`rv64_production_wm_producer.spl`, `wm_codec.spl`, `backend_vulkan_helpers.spl`,
`metal_session.spl` newly appear; `window_scene_draw_ir.spl` moved line
196->202). This confirms the doc's core claim: nothing runs this gate, so
violations keep accumulating silently. The guard itself
(`scripts/check/check-wm-lane-boundary.shs`) is still not wired into
`pre-push-conflict-tree-guard.shs`.

Of the 5 originally-listed sites, only `src/app/wm_showcase/session.spl`
lines 51/61-64 are in this session's scope (`src/app/**`); the other 2
original sites and all 6 newly-appeared sites are in `src/lib/**`/`src/os/**`,
out of scope. The `session.spl` violations are `use` imports of
`app.wm_showcase_host.host_compositor_entry` (line 51) and
`std.gc_async_mut.gpu.browser_engine.simple_web_renderer` /
`simple_web_html_layout_renderer_foundation` (lines 61-64) — these are the
showcase's actual rendering-backend dependencies, called out in the file's
own header comment as deliberate (interpreted HTML renderer reuse, "out of
this showcase's scope" to change). Removing them would break the showcase's
functionality; the doc's own "Next step" section frames the real remedy as
either fixing the sites (an architecture decision, not a mechanical patch)
or re-baselining with justification — explicitly an "owner decision needed",
not something to silently resolve in a scan-and-patch pass.

**Classification: NOT-FIXED, re-confirmed and WORSE (11 vs 7).** No source
changes made — fixing `session.spl`'s lane-boundary imports without
coordinated changes to the (out-of-scope) rendering backend would either
break the showcase or require an architectural lane split beyond this
session's authority to decide unilaterally. Re-baselining
`doc/08_tracking/wm_lane_boundary_baseline.txt` was considered and rejected
for the same reason: it is not a `doc/08_tracking/bug/` doc and the doc
itself frames re-baselining as requiring "an explicit, reviewed
justification for each new entry" — a judgment call outside this pass's
remit. Status remains open; violation count updated 7 -> 11 in this note.



---

## Follow-up Fix & Verification (2026-11-26, Windows Host / `release/1.0.0`)

- **Gate script Windows E2BIG fix** (`scripts/check/check-wm-lane-boundary.shs`, `scripts/check/scan_guard_vacuity_baseline.txt`):
  - Batched `scan.txt` into `<=20000`-byte shards against an empty baseline and aggregated violations before comparing once against `doc/08_tracking/wm_lane_boundary_baseline.txt`, eliminating `rc=126` (`Argument list too long`) on Windows MSYS.
  - Added counted verdict output (`PASS — $FILE_COUNT file(s) scanned, ...`) and removed `check-wm-lane-boundary.shs` from `scripts/check/scan_guard_vacuity_baseline.txt`.
- **Code fixes for the 3 surfaced `WML001` violations** (without modifying `doc/08_tracking/wm_lane_boundary_baseline.txt`):
  1. `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`: replaced all 4 `time_now_micros()` trace calls in `present()` with `default_frame_clock().now_micros()` and removed `use std.nogc_sync_mut.io.time_ops.{time_now_micros}`.
  2. `src/lib/gc_async_mut/gpu/engine2d/engine.spl` + `src/lib/gc_async_mut/gpu/engine2d_host_io.spl`: routed `env_get`, `platform_name`, `file_exists`, and `file_read_bytes_result` through the sibling `gpu` render-sublane host adapter `std.gc_async_mut.gpu.engine2d_host_io` (also recorded in `src/lib/source_inventory.lock`).
  3. `src/lib/gc_async_mut/gpu/browser_engine/script/script_runner.spl` + `src/lib/gc_async_mut/gpu/browser_js_host.spl`: routed `JsRuntime`, `js_runtime_with_default_logger`, and `NATIVE_*` bridge IDs through the sibling `gpu` render-sublane adapter `std.gc_async_mut.gpu.browser_js_host` (also recorded in `src/lib/source_inventory.lock`).
- **Verification**:
  - `sh scripts/check/check-wm-lane-boundary.shs`: `PASS — 619 file(s) scanned, 148 violation(s), all in baseline (4 baseline entr(y/ies) now fixed)` (exit `0`).
  - `sh scripts/audit/wm-lane-boundary-sffi-authority.shs`: `PASS` (exit `0`).
  - `sh scripts/check/check-tierless-std-js-imports.shs`: `PASS — 141 tier-less std.js import(s) checked, common/js=1, baseline 141` (exit `0`).
  - `sh scripts/audit/direct-env-runtime-guard.shs --working`: `STATUS: PASS direct-env-runtime-guard` (exit `0`).
  - Targeted interpreter specs (`--mode=interpreter`): `wm_lane_boundary_spec.spl` (5/5), `wm_lane_boundary_layering_prevention_spec.spl` (4/4), `page_scripts_bom_globals_spec.spl` (15/15), `script_dom_bridge_spec.spl` (4/4), `host_bug_a07_baremetal_backend_probe_spec.spl` (4/4), `vulkan_renderer_spec.spl` (4/4), `facade_export_use_targets_exist_spec.spl` (4/4), `draw_text_bg_spec.spl` (4/4).
  - `lint --fast --jobs=1` on all 5 touched `.spl` files: 0 errors, exit `0`.
