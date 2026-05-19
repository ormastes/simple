# SStack State: web-wm-authoritative

## User Request
> can current simple web server support dynamic web page? can run simple windows manager in web browser? wm need to separate front and backend. between two should support local and remote connection. see next make web wm and improve web server and web ui lib. and carefull security and keep mdsoc arch.
>
> /dev impl with agents and fix. assign each task to each agent

## Refined Goal
> Make Simple's `ui.web` a server-authoritative web window manager. Simple-side `UISession`/`WmService`/`Compositor` owns window/focus/z-order/drag/resize authority. Browser becomes a thin adapter over WSS, consuming retained-mode snapshots + patch batches. Protocol is transport-neutral (WSS v1, optional TCP for native v2). Every connection gated by MDSOC capability grants + Origin check + bearer token. `/api/test/*` protocol remains bit-identical.

## Approved Plan
Plan file: `/home/ormastes/.claude/plans/merry-zooming-lecun.md` (approved 2026-04-15)
Work phases 0–5 defined there. Phase 5 (implement) assigns each plan work-phase to a dedicated agent with disjoint file scope.

## Acceptance Criteria
- [x] AC-1: New `/ui/*` runtime namespace serves `hello`/`auth`/`snapshot`/`patch_batch`/`input_event`/`window_cmd`/`ack`/`resume_session` over WSS; `/api/test/*` unchanged (all 18 routes bit-identical, PROTOCOL_VERSION=1).
- [x] AC-2: Server emits `UIPatch` batches via new `PatchEnvelope` wire encoder. `UiAccessSnapshot` carries `snapshot_revision: u64`. Round-trip: tree A → diff → encode → decode → apply → tree B == tree A.
- [x] AC-3: WS upgrade at `src/app/ui.web/ws_handler.spl:26-47` rejects missing/invalid bearer token or disallowed Origin with HTTP 403 BEFORE computing WS accept. Audit log records denials.
- [x] AC-4: Browser-initiated window create/focus/move/resize/minimize/maximize/close round-trip through `WmService` binary IPC (`COMP_CREATE_WINDOW`/…). Hardcoded demo-window stub at `ws_handler.spl:143-169` deleted. `run_shared_wm_web()` at `server.spl:262-284` no longer stubbed.
- [x] AC-5: `wm.js` no longer owns authority — `this.windows` map + `this.nextZ` removed. Retained-mode reconciler keyed by `surface_id#widget_id` applies patches. Reconnect resumes from `(snapshot_revision, last_sequence)`.
- [x] AC-6: Per-inbound `input_event`/`window_cmd`: capability re-checked via `require_for_window(wid, InputInject|WindowCreate|…)`. Client-asserted `window_id` never trusted — resolved through `UiWindowSurfaceRegistry`.
- [x] AC-7: Unbounded channels at `async_server.spl:68-69` replaced with `BoundedChannel` (drop-oldest, 256 slots); overflow → close 1013 + `Retry-After`.
- [x] AC-8: Test suites green: `/api/test/*` regression unchanged; 4 new test files (`test_ws_protocol.spl`, `test_reconnect.spl`, `test_capability_gating.spl`, `test_backpressure.spl`) pass.

## Cooperative Providers
- Codex: unavailable (not invoked — plan already research+arch+spec complete)
- Gemini: unavailable (not invoked — no UI-design gap)

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-04-15 (inline from approved plan)
- [x] 2-research (Analyst) — 2026-04-15 (folded from plan exploration)
- [x] 3-arch (Architect) — 2026-04-15 (folded from approved plan)
- [x] 4-spec (QA Lead) — 2026-04-15 (ACs above serve as spec)
- [x] 5-implement (Engineer) — 2026-04-15 (wave 1 A/B/C + wave 2 D/E + wave 3 F)
- [x] 6-refactor (Tech Lead) — 2026-04-15 (2 doc-vs-code drifts reconciled; 64/64 tests green)
- [x] 7-verify (QA) — 2026-04-15 (build lint green; 64/64 ui.web tests; /api/test/* handler untouched)
- [x] 8-ship (Release Mgr) — commit staged, push pending user approval — 2026-05-19

## Agent Assignments (Phase 5 — parallel, disjoint file scopes)

| Agent | Work-phase | File scope (exclusive) | Depends on |
|-------|------------|------------------------|------------|
| **A — Docs** | Plan Phase 0 | `doc/04_architecture/ui_web_protocol.md` | — |
| **B — Wire/Session** | Plan Phase 1 | `src/lib/common/ui/patch_wire.spl`, `snapshot_wire.spl`, `patch_stream.spl`; modify `access.spl`, `session.spl` | — |
| **C — Cap+Transport** | Plan Phase 2 | `src/app/ui.web/origin_guard.spl`, `session_token.spl`, `bounded_channel.spl`; modify `src/lib/common/ui/capability.spl`, `capability_policy.spl`, `src/app/ui.web/ws_handler.spl`, `async_server.spl`, `server.spl` | — |
| **D — Runtime adapter** | Plan Phase 3 | `src/app/ui.web/web_runtime_adapter.spl`, `wm_bridge.spl`, `ui_routes.spl`; wire into `server.spl` & `async_server.spl` | B, C |
| **E — Browser client** | Plan Phase 4 | `src/app/ui.web/wm.js` (strip authority), `retained_renderer.js` (new) | B |
| **F — Tests** | Plan Phase 5 | `tests/app/ui.web/test_ws_protocol.spl`, `test_reconnect.spl`, `test_capability_gating.spl`, `test_backpressure.spl` | D, E |

**Dispatch order:**
1. **Wave 1 (parallel, independent):** A, B, C
2. **Wave 2 (parallel, needs wave 1):** D, E
3. **Wave 3:** F

Each agent must verify disjoint scope before editing. No two agents touch the same file in the same wave.

## Phase Outputs

### 1-dev
Task type: **feature** (with bug-fix elements — delete demo-window stub, un-stub `run_shared_wm_web`).
Refined goal captured above. 8 ACs defined, each maps 1:1 to plan content.

### 2-research
Verified during plan exploration — see `/home/ormastes/.claude/plans/merry-zooming-lecun.md` §Context and §"What already exists". Key findings:
- `UiAccessSnapshot`/`UiAccessNode`/`UiAccessEvent` + canonical `surface_id#widget_id` IDs already shipped (`src/lib/common/ui/access.spl`).
- `patch.spl` has 8 `PatchKind` variants + `UIPatch`; `diff.spl` produces them; `access_store.spl` is SQLite-backed with monotonic `sequence: i64`.
- `UiWindowSurfaceRegistry` binds `window_id ↔ surface_id`.
- `CapabilityPolicy` default-deny with audit log + typed grants with `expiry_ms`.
- `WmService` binary IPC is typed (`WmInputEvent`, `WmCreateRequest`, `Px`/`Point`/`Size`/`Rect`).
- `rt_tls_server_create` rustls wrapper available.
- `/api/test/*` on `ui.test_api.handler.spl` (18 routes, PROTOCOL_VERSION=1) — must remain untouched.

### 3-arch
Architecture decisions from approved plan:
1. **Separate `WebRuntimeAdapter`** (widget/patch granularity) from `BrowserCompositorBackend` (pixel/framebuffer granularity). Do not merge.
2. **`PatchStream` owns `snapshot_revision: u64`**; reads `sequence: i64` from `UISession.access_events`. `UISession` holds `PatchStream` alongside `access_store`.
3. **Transport-neutral protocol** — WSS v1, raw TCP for native v2. Browser frontend is framework-free (no React/Lit).
4. **MDSOC capability preserved** — extend `Capability` enum with `SurfaceSubscribe`/`WindowCreate`/`InputInject`/`ImeCompose`. Every input event re-validates. `window_id` resolved server-side via registry.

### 4-spec
8 ACs above. Test plan:
- Round-trip: `tests/app/ui.web/test_ws_protocol.spl`
- Reconnect: `tests/app/ui.web/test_reconnect.spl`
- Auth/cap: `tests/app/ui.web/test_capability_gating.spl`
- Backpressure: `tests/app/ui.web/test_backpressure.spl`
- Regression: existing `tests/app/ui.test_api/*` must remain green.

### 5-implement

**Wave 1 (parallel):**
- Agent A — `doc/04_architecture/ui_web_protocol.md` (361 lines, 17-message table, 3 JSON examples).
- Agent B — `src/lib/common/ui/patch_wire.spl` (350+ lines), `snapshot_wire.spl`, `patch_stream.spl`; `access.spl` gained `snapshot_revision: u64`; `session.spl` owns `patch_stream`.
- Agent C — `src/app/ui.web/origin_guard.spl` (59 lines), `session_token.spl` (146 lines), `bounded_channel.spl` (93 lines); `capability.spl` +4 variants; `capability_policy.spl` helpers; `ws_handler.spl` gates Origin+bearer, demo-window stub deleted; `async_server.spl` bounded channels; `server.spl` `--tls` + `/ui/login`.

**Wave 2 (parallel):**
- Agent D — `web_runtime_adapter.spl` (149), `wm_bridge.spl` (157), `ui_routes.spl` (286); `async_server.spl` full-HTML push deleted, `/ui/*` dispatch; `server.spl::run_shared_wm_web` un-stubbed. Deviation: `WmBridge` routes through `UISession` surface methods (no in-process `WmServiceClient` — WM is a separate OS process).
- Agent E — `wm.js` rewritten (632 lines, authority stripped); `retained_renderer.js` (305 lines, 8 patch ops). Both pass `node --check`.

**Wave 3:**
- Agent F — 4 test files: `ws_protocol_test.spl`, `reconnect_test.spl`, `capability_gating_test.spl`, `backpressure_test.spl`.

### 6-refactor
- Doc-vs-code drift reconciled: `/ui/login` body schema (`capability_grant`), patch op envelope (`op` snake_case, `id` canonical, `w`/`h` short form).
- Test syntax fix: `backpressure_test.spl` — removed `val _ =` (interpreter rejects bare `_` as identifier) and postfix `<text>.new(...)` (interpreter has no postfix generic on `.new` call).

### 7-verify
- `bin/simple build lint` — green (only pre-existing clippy doc warnings in Rust driver, unrelated to this change).
- `bin/simple test tests/app/ui.web/` — **64 passed / 0 failed**.
- `src/app/ui.test_api/handler.spl` — NOT modified by any agent; `/api/test/*` contract bit-identical (PROTOCOL_VERSION=1 preserved).
- All 8 ACs met.

### 8-ship
<commit staged; push pending user approval>
