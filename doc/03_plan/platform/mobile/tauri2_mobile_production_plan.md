# Plan — Tauri 2 Mobile (iOS + Android) Production Readiness

**Date:** 2026-07-07 · **Status:** OPEN — agent-executable · **Domain:** platform/mobile
**Design pair:** [`doc/05_design/platform/mobile/tauri2_mobile_production_design.md`](../../../05_design/platform/mobile/tauri2_mobile_production_design.md)
**Author role:** plan author (doc-only; integrator commits)

Each item: **motivation + evidence · files · steps · specs/gates · size (S/M/L) · deps · risks + rollback.**
"Verified 2026-06-06/07-02" evidence may have rotted — **Phase 0 re-verifies before any new build.**

Dependency spine: `P0.1 (recover shell source)` → `P1 (re-verify lanes)` → `P2 (harden sim/emulator
to production)` → `P3 (iOS device AOT, gated on Task #21)` + `P4 (release lanes)` → `P5 (perf + OTA)`.

---

## Phase 0 — Recover state / stop the bleeding (do first)

### P0.1 — Recover & commit the Tauri shell source **[BLOCKER]** — DONE (2026-07-07)
- **Resolution:** restored via `git checkout c8756fe7cc -- tools/tauri-shell` (last
  commit with the complete tree, root-caused in
  `doc/09_report/tauri_shell_source_recovery_investigation_2026-07-07.md` as
  deleted by mislabeled commit `c8dbb4df4f`, 36s later). 132 files recovered.
  Reconciled against the untracked sibling checkout `simple-renderer-main`
  found during investigation — diff showed git's tree was already a strict
  superset (has the sibling's MDI-proof fields/functions *and* the
  `libc::signal(SIGPIPE, SIG_IGN)` fix *and* the `libc` dep the sibling
  lacks), so no porting was required. `cargo check` in `src-tauri` compiles
  clean (host target). See the bug record's "Recovery" section for the full
  diff evidence and the correction to the investigation's Lane 3 claim.
- **Motivation/evidence:** `git ls-files tools/tauri-shell` = **14 files, all `gen/**` scaffolding**.
  The production shell (`src-tauri/src/{app,main,lib}.rs`, `Cargo.toml`, `build.rs`, top-level
  `tauri.conf.json`, `dist/*.html`, `scripts/build-ui-bundle.shs`) is **untracked and absent from the
  main WC**. The app is not reproducible from a clean checkout. (design §0a)
  Filed as [`doc/08_tracking/bug/tauri_shell_source_untracked_unreproducible_2026-07-07.md`](../../../08_tracking/bug/tauri_shell_source_untracked_unreproducible_2026-07-07.md).
- **Files:** create/restore `tools/tauri-shell/src-tauri/src/{app,main,lib}.rs`,
  `src-tauri/Cargo.toml`, `src-tauri/build.rs`, `src-tauri/tauri.conf.json`, `dist/index.html` +
  `dist/inline-shell.html`, `scripts/build-ui-bundle.shs`. Update `.gitignore` only if it is
  currently ignoring source (it is not — it ignores blobs/build output; verify `.gitignore:225-241`).
- **Steps:** (a) locate the last-known-good source — search jj/git history
  (`jj log`, `git log --all -- tools/tauri-shell/src-tauri/Cargo.toml`), the two on-disk binary blobs'
  build provenance, and any archived worktree; (b) if unrecoverable, reconstruct from the generated
  `gen/**` + the guide's documented behavior; (c) `jj commit` the source (NOT `target/`, NOT
  `ui_bundle.tar.gz`, NOT `*.bin`); (d) confirm `cargo build` from a clean checkout.
- **Gate:** fresh `git clone`/checkout + `cargo tauri android build --debug` reaches an APK **without**
  any file from the developer's dirty WC. No `target/`, `*_bundle.tar.gz`, or `*_runtime_*.bin` enter
  git (`.gitignore:229-241` guards these — verify range).
- **Size:** M (L if source is truly lost and must be reconstructed). **Deps:** none.
- **Risks/rollback:** committing build artifacts re-bloats the WC (the ~298k-file incident,
  `.gitignore:237` note) — guard with the tracked-file count check. Rollback: revert the commit; the
  gen/** scaffolding is unchanged.

### P0.2 — Re-verify the parity gate actually runs (anti-rot)
- **Motivation/evidence:** the parity report is dated 2026-07-02 and self-declares "retained ≠ pass;
  rerun required" (`tauri_mobile_guide.md:210-218`). The 06-06 "verified live" claim is a month old.
- **Files:** run `scripts/check/check-tauri-mobile-renderer-parity-evidence.shs` (+ direct
  `check-tauri-ios-*` / `check-tauri-android-*` wrappers). No edits — a health probe.
- **Steps:** boot iPhone sim + Pixel AVD, run the aggregate wrapper, capture fresh
  `doc/09_report/tauri_mobile_renderer_parity_evidence_2026-07-07.md`.
- **Gate:** either all §7 design gates pass **fresh today**, or the failing lane is filed as a bug in
  `doc/08_tracking/bug/` with the exact validator row that failed. No green claim without today's run.
- **Size:** S. **Deps:** P0.1 (needs a buildable shell). **Risk:** emulator/SDK drift; rollback n/a.
- **Partial re-verify 2026-07-08:** direct (non-wrapper) build+install+launch+capture check —
  see `doc/09_report/mobile_p0_lane_reverification_2026-07-08.md`. iOS sim and Android emulator
  builds both `BUILD SUCCEEDED`/APK+AAB produced, install+launch clean, render pipeline fires
  (`[tauri-shell] render, html_len=336705` + `eval OK` on **both** platforms), but the captured
  screen is **blank white** on both — not the styled dark showcase the retained evidence claims.
  The aggregate wrapper itself was not run (out of timebox). Treat the 07-02 retained "pass" as
  **not reconfirmed**; recommend filing a blank-paint regression bug before P1.2/P1.3 proceed.
- **RESOLVED 2026-07-07 (integration pass):** root cause was a duplicate, broken
  `parse_ui_to_tree(path)` in `src/lib/common/ui/parse/sdn_tree.spl` that ignored `path` and
  always parsed `""`, colliding at the cross-module symbol level with the correct
  `nogc_sync_mut.ui.parse.sdn_tree.parse_ui_to_tree` — see
  `doc/08_tracking/bug/tauri_mobile_webview_blank_white_render_2026-07-08.md` (now FIXED). Fix:
  deleted the broken stub and repointed `glass_pipeline_compare.spl`'s import to the correct
  implementation. Desktop-lane verification (regenerate `render_mobile_page.spl` → 346,701 bytes
  full widget tree; headless Chrome 390×844 screenshot 100% non-white, visually confirms styled
  nav/tabs/dialog/bottom-sheet) confirms the render-pipeline blank-paint bug is fixed. **Not yet
  re-confirmed end-to-end on-device/on-simulator**: the mobile shell loads content via an
  embedded/bundled `simple` runtime subprocess (baked in via `include_bytes!`), not via the
  `dist/index.html` static asset directly, so a full P0.2 aggregate-wrapper rerun still requires
  rebuilding+re-embedding that bundled runtime with this fix before iOS/Android screenshots will
  reflect it. That rebuild-and-rerun is the remaining P0 acceptance step blocking P1.2/P1.3.

---

## Phase 1 — Close the simulator/emulator honesty gaps

### P1.1 — Reconcile responsive breakpoints (single source of truth)
- **Motivation/evidence:** guide says CSS breakpoints 600/**1200** (`tauri_mobile_guide.md:93-96`);
  code `default_breakpoints()` regular boundary is **840** (`profile.spl:56`). Production needs one
  number. (design §5)
- **Files:** `src/app/ui/web/html.spl` (`generate_css` media queries), `src/lib/common/ui/profile.spl`,
  `doc/07_guide/platform/mobile/tauri_mobile_guide.md`.
- **Steps:** dump what `generate_css` actually emits; decide 840 (code, Material-aligned) as truth;
  align CSS + guide prose; add a spec asserting emitted `@media` widths == `default_breakpoints()`.
- **Gate:** new spec under `test/**/ui/` asserting media-query widths match `profile.spl`; guide text
  updated. **Size:** S. **Deps:** none. **Risk:** low; rollback = revert.

### P1.2 — Establish/verify the mobile `invoke()` back-channel over `app://`
- **Motivation/evidence:** two-way `invoke()` needs an `app://` custom-scheme build (project memory
  2026-06-04); no in-repo mobile proof (design §3b, App. B). Today's live mode is stdio one-way + DOM
  events back over stdin — works on sim/emulator but the native-command return path is unproven on mobile.
- **Files:** `tools/tauri-shell/src-tauri/src/app.rs` (command handlers + custom protocol),
  `dist/inline-shell.html` (invoke calls), `src/app/ui.ipc/*`.
- **Steps:** build with the `app://` scheme; add a round-trip command (webview `invoke("ping")` →
  native → value back); capture the returned value in the MDI proof JSON.
- **Gate:** MDI proof gains an `invoke_roundtrip_status=pass` field on both lanes, backed by a real
  returned value (not `eval OK`). **Size:** M. **Deps:** P0.1. **Risk:** if `app://` regresses ATS/asset
  loading on iOS, keep the `tauri://` asset path (`tauri_mobile_guide.md:72-77`); rollback = drop the
  command, keep one-way IPC.

### P1.3 — Background/foreground lifecycle
- **Motivation/evidence:** no evidence lifecycle is handled; desktop window APIs are `#[cfg(desktop)]`
  and absent on mobile (design §4b, `tauri_simple_integration_status_2026-03-23.md:160-166`).
- **Files:** `tools/tauri-shell/src-tauri/src/lib.rs` (mobile entry), Simple render-loop pause hook.
- **Steps:** on background, pause the subprocess/render loop; on foreground, re-emit last render
  envelope (renderer is idempotent). Add a suspend→resume probe to the evidence wrapper.
- **Gate:** a `lifecycle_resume_status=pass` row: after backgrounding + foregrounding, a fresh
  `[tauri-shell] render, html_len=` marker appears and the screenshot is nonblank. **Size:** M.
  **Deps:** P0.1. **Risk:** platform-specific event names; rollback = no-op resume (re-render always).

---

## Phase 2 — Production-harden the emulator/simulator lanes

### P2.1 — Backend-isolation lint clean for `src/app/ui.tauri/**`
- **Motivation/evidence:** isolation gate greps `src/app/**` for App→backend-impl / App→`rt_*`
  (`backend_isolation_architecture.md:81-83`). Mobile must stay clean (design §9). `backend.spl` uses
  only the sanctioned `rt_stdin_read_line` transport extern (`backend.spl:38`).
- **Files:** the isolation lint allowlist (plan P2 of backend_isolation_plan), `src/app/ui.tauri/**`.
- **Steps:** run the lint over `ui.tauri`; if `rt_stdin_read_line` trips it, add it to the transport
  allowlist (it is an IPC boundary, not a render backend). **Gate:** lint passes on `ui.tauri/**`.
  **Size:** S. **Deps:** none. **Risk:** none; rollback = allowlist entry.

### P2.2 — Guest-Vulkan (real device GPU) Android evidence
- **Motivation/evidence:** current green Android lane is **host/emulator Vulkan translation, not guest
  `skiavk`** — Pixel7 AVD crashes `libhwui`/`VulkanManager` under guest skiavk/swiftshader/lavapipe
  (`tauri_mobile_guide.md:228-230`). Production needs real-GPU proof.
- **Files:** evidence wrappers; test on a real Android device or a working guest-GPU AVD.
- **Steps:** run the Android lane on physical hardware; capture guest Vulkan markers + screenshot.
- **Gate:** `android_gpu_context=guest-vulkan` (not host-translation) in the proof. **Size:** M.
  **Deps:** P0.1, physical device. **Risk:** hardware access; rollback = keep host-translation label,
  do not overclaim.

---

## Phase 3 — iOS device (AOT static-link) **[gated]**

### P3.1 — AOT-compile the Simple UI closure for `aarch64-apple-ios`
- **Motivation/evidence:** iOS device forbids subprocess-spawn + JIT; the live mode spawns
  `simple run …` and the embedded runtime is **sim-only** (`ios_runtime_aarch64_sim.bin`)
  (design §1b; `tauri_mobile_guide.md:55,69-71`).
- **Files:** build tooling for an `aarch64-apple-ios` (device) static archive of `src/app/ui/main.spl`
  + module closure; a C-ABI shim exporting `render_ipc(sdn) -> json` and `send_action(json)`.
- **Steps:** (a) produce a compiled (LLVM/`native`) frontend build of the UI closure for the device
  triple; (b) wrap it as a static lib; (c) link it into the shell like the existing
  `gen/apple/Externals/arm64/debug/libapp.a`; (d) shell calls Simple **in-process** — no `Command`
  spawn on iOS.
- **Gate:** a device build with **zero** subprocess spawn on the iOS path; render envelope produced by
  the in-process entry; smoke on a real iPhone (foreground + nonblank capture + routed touch).
- **Size:** L. **Deps:** **Task #21** — compiled self-hosted frontend
  (`doc/03_plan/compiler/self_hosted_frontend/full_cli_redeploy_and_browser_startup_plan.md`, §0:
  interpreted frontend is `~0.8 ms/char`, blocking compiled builds). **Do not start P3.1 until #21's
  Track A/B land.**
- **Risks/rollback:** if AOT is not ready, iOS ships **simulator-only** (honest limitation, already the
  status); rollback = keep the sim lane, do not claim device support.

### P3.2 — iOS device signing + TestFlight lane
- **Motivation/evidence:** sim build is unsigned (`CODE_SIGNING_*: NO`,
  `tauri_mobile_guide.md:130-137`); device needs a team + profile.
- **Files:** `gen/apple/project.yml` (flip signing on, set `DEVELOPMENT_TEAM`), then
  **`xcodegen generate`** (mandatory, `tauri_mobile_guide.md:114-118`).
- **Steps:** archive → export signed `.ipa` → TestFlight upload; keep secrets out of git.
- **Gate:** a TestFlight build installs on a real device and renders. **Size:** M. **Deps:** P3.1,
  Apple team. **Risk:** signing config regresses the sim build — keep the sim/device split via
  `$(PLATFORM_NAME)` (`tauri_mobile_guide.md:129`); rollback = revert project.yml + re-`xcodegen`.

---

## Phase 4 — Release lanes (parallelizable with Phase 3)

### P4.1 — Android release AAB + Play internal track
- **Motivation/evidence:** current build is `--debug` universal APK (`tauri_mobile_guide.md:170-172`);
  Play needs a signed AAB. (design §2a)
- **Files:** `gen/android` gradle signing config (keystore via env/secret), release build script (`.shs`).
- **Steps:** `cargo tauri android build --release` → signed AAB → Play internal testing.
- **Gate:** signed AAB uploads to Play internal track and installs. **Size:** M. **Deps:** P0.1.
  **Risk:** keystore mishandling; rollback = debug APK lane unaffected.

### P4.2 — Version/identifier wiring
- **Motivation/evidence:** identifier `com.simple.ui`; version lives in `tauri.conf.json` /
  `tauri.properties`. (design §8)
- **Files:** `tauri.conf.json`, `gen/android/app/tauri.properties`.
- **Steps:** single source for version; bump script; ensure IPC envelope fields stay additive.
- **Gate:** version string matches across Android/iOS artifacts. **Size:** S. **Deps:** P0.1.

---

## Phase 5 — Performance, memory, and update strategy

### P5.1 — Cold-start / RSS baseline + ceilings
- **Motivation/evidence:** no honest cold-start/RSS numbers exist; only in-webview timing deltas
  (design §6). Ceilings in §6 are ASSUMPTIONs until measured.
- **Files:** a measurement `.shs` capturing `am start`/`simctl launch` → first render marker; meminfo.
- **Steps:** 3 cold starts per device class, median; record device/OS/GPU-mode; set real ceilings.
- **Gate:** a perf spec under `test/**/05_perf/` with measured numbers; CI-comparable. **Size:** M.
  **Deps:** P0.1. **Risk:** noisy emulator numbers — require physical-device numbers for iOS device
  ceilings; rollback n/a (measurement only).

### P5.2 — Data-only OTA UI update policy (store-compliant)
- **Motivation/evidence:** stores forbid shipping executable code that self-updates; renderer must
  stay in the signed binary (design §8).
- **Files:** doc-level policy + any UI-asset fetch path (must be `.ui.sdn`/CSS **data only**).
- **Steps:** if OTA is pursued, restrict payload to declarative scene data; no new native code.
- **Gate:** a lint/review rule that OTA payloads contain no executable. **Size:** S. **Deps:** none.

---

## Risk register (cross-cutting)

| Risk | Trigger | Mitigation |
|---|---|---|
| WC re-bloat | committing `target/`/blobs in P0.1/P4 | tracked-file-count guard; `.gitignore:229-241` |
| Overclaimed evidence | reusing retained parity report | Phase 0.2 rerun; "retained ≠ pass" enforced (`tauri_mobile_guide.md:210` ) |
| iOS device slips | Task #21 not done | ship sim-only, state it plainly; P3 is gated, not assumed |
| Host-Vulkan mistaken for guest-GPU | Android green on emulator | label host-translation explicitly (P2.2) |
| xcodegen not re-run | project.yml edited, build reuses stale `.xcodeproj` | every iOS signing/settings change ends with `xcodegen generate` |

## Anchors
- Design: `doc/05_design/platform/mobile/tauri2_mobile_production_design.md`
- Guide: `doc/07_guide/platform/mobile/tauri_mobile_guide.md`
- Isolation: `doc/04_architecture/ui/rendering/backend_isolation_architecture.md`
- iOS-AOT dep (Task #21): `doc/03_plan/compiler/self_hosted_frontend/full_cli_redeploy_and_browser_startup_plan.md`
- Code: `src/app/ui.tauri/backend.spl`, `src/lib/common/ui/{profile,form_factor}.spl`
</content>
