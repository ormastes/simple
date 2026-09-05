# Tauri 2 Mobile (iOS + Android) — Production Design

**Date:** 2026-07-07 · **Status:** DESIGN (production target) · **Domain:** platform/mobile
**Author role:** plan/design author (doc-only; integrator commits)

**Reads-with:**
- Plan: [`doc/03_plan/platform/mobile/tauri2_mobile_production_plan.md`](../../../03_plan/platform/mobile/tauri2_mobile_production_plan.md)
- Dev guide (current how-to): [`doc/07_guide/platform/mobile/tauri_mobile_guide.md`](../../../07_guide/platform/mobile/tauri_mobile_guide.md),
  [`ios_dev_guide.md`](../../../07_guide/platform/mobile/ios_dev_guide.md), [`android_dev_guide.md`](../../../07_guide/platform/mobile/android_dev_guide.md)
- Backend isolation contract: [`doc/04_architecture/ui/rendering/backend_isolation_architecture.md`](../../../04_architecture/ui/rendering/backend_isolation_architecture.md)
- Historical status (superseded): [`../tauri_simple_integration_status_2026-03-23.md`](../tauri_simple_integration_status_2026-03-23.md)
- iOS-AOT dependency: [`doc/03_plan/compiler/self_hosted_frontend/full_cli_redeploy_and_browser_startup_plan.md`](../../../03_plan/compiler/self_hosted_frontend/full_cli_redeploy_and_browser_startup_plan.md) (Task #21)

> **Honesty banner.** Every "verified" statement below is dated and cites a repo artifact. Retained
> evidence is *not* a standing pass — the mobile parity gate itself states evidence must be re-run
> after any renderer/shell/runtime/SDK change (`tauri_mobile_guide.md:211-218`). Two blocking
> production gaps are flagged in §0 up front so they are not lost in detail.

---

## 0. Two blocking facts a reader must know first

**(0a) The Tauri shell's own source is NOT in git / NOT on disk in the main working copy.**
`git ls-files tools/tauri-shell` returns **14 files, all `gen/android` + `gen/apple` scaffolding**
(generated Kotlin, `tauri.*.gradle`, one `gen/android/.../assets/tauri.conf.json`). The
production-critical shell sources — `src-tauri/src/{app,main,lib}.rs`, `src-tauri/Cargo.toml`,
`src-tauri/build.rs`, top-level `src-tauri/tauri.conf.json`, `dist/*.html`, and
`scripts/build-ui-bundle.shs` — are **absent from the main WC** (only `target/` build artifacts and
the two gitignored binary blobs remain on disk). `.gitignore:225-241` gitignores the generated
`ui_bundle.tar.gz` and `ios_runtime_aarch64_sim.bin`, but the *source* is simply untracked. The
dev guide (`tauri_mobile_guide.md`) documents these files as if present. **Consequence: the app is
not reproducible from a clean checkout of `main`.** This is Phase 0 P0 in the plan.

**(0b) iOS is SIMULATOR-ONLY; there is no physical-device evidence.** The embedded iOS runtime is
`src-tauri/ios_runtime_aarch64_sim.bin` — an `aarch64-apple-ios-sim` build
(`tauri_mobile_guide.md:69-71`). The live mode **spawns a subprocess** (`simple run <cache>/…`,
`tauri_mobile_guide.md:55`), which iOS forbids on a real device (no `fork`/`exec` of a second
executable; no JIT W^X pages without a special entitlement). Device support therefore requires the
compiled frontend **statically linked into the shell** with no subprocess — which depends on Task
#21 (§1b, §3 dependency chain).

---

## 1. Runtime strategy per platform

The invariant across all lanes: **the same Simple UI library renders desktop, web, and both mobile
webviews** — one widget tree, one `render_html_tree` → `generate_css` HTML/CSS pipeline
(`tauri_mobile_guide.md:22-26`; `ui.tauri/backend.spl:40-52`). Only the *runtime host* differs.

### 1a. Android — subprocess/interpret allowed (current live path)

Android permits spawning a child process and loading a `.so`, so the live path works today:

- The cross-compiled Simple runtime ships as a JNI library:
  `gen/android/app/src/main/jniLibs/arm64-v8a/libsimple_mobile_runtime_exec.so` (present on disk).
- On launch the shell extracts the embedded `ui_bundle.tar.gz` to `<cache>/ui-bundle/bundle/` and
  runs `simple run <cache>/src/app/ui/main.spl tauri <cache>/<showcase>.ui.sdn`
  (`tauri_mobile_guide.md:48-59`). Render IPC flows over stdout; DOM events return over stdin.
- Module resolution is `find_project_root` (walks up for `src/`), **not** `SIMPLE_LIB` — hence the
  `<cache>/src/...` layout (`tauri_mobile_guide.md:63-66`).
- **Execution mode:** interpret is acceptable on Android for correctness. JIT is *allowed* by the OS
  but is not required and not the parity target; the honest performance path is the same compiled
  frontend as iOS (§1b) once Task #21 lands. ASSUMPTION (not re-measured this week): current Android
  runtime is the interpreter; cold-start numbers in §6 must be captured, not asserted.

### 1b. iOS device — NO JIT, NO subprocess → AOT static-link (target, not yet built)

The iOS **simulator** reuses the Android-style subprocess model with a sim runtime blob
(`ios_runtime_aarch64_sim.bin`). A **real device** cannot:

| iOS device constraint | Why the current path breaks | Production resolution |
|---|---|---|
| No second-process `exec` | live mode spawns `simple run …` | Link the frontend **into** the shell binary; call it in-process (FFI), no spawn |
| No JIT (W^X enforced) | interpreter is fine, but a JIT/Cranelift path is not | Run **AOT-compiled** Simple (LLVM/`native` backend), interpret-only fallback in-process |
| App is a single signed Mach-O | can't drop a `simple` binary next to assets | Static-link `libapp`-style archive (cf. `gen/apple/Externals/arm64/debug/libapp.a` already exists for the shell's own Rust) |

**AOT plan shape** (design intent; execution in plan Phase 3):
1. Compile the Simple UI closure (`src/app/ui/main.spl` + its module set) **ahead of time** for
   `aarch64-apple-ios` (device triple, not `-sim`) into a static archive.
2. Expose a single C-ABI entry (`render_ipc(sdn_path) -> json`, and a `send_action(json)` sink) so
   the Rust shell calls Simple **in-process** instead of spawning.
3. The app shell = Rust/Tauri webview host + statically-linked Simple archive + embedded `.ui.sdn`
   assets. No `ui_bundle.tar.gz` extraction, no `find_project_root` on device (the module graph is
   resolved at compile time).
4. **Hard dependency:** step 1 needs the self-hosted frontend to run **compiled**, not interpreted.
   That is exactly Task #21 in
   `full_cli_redeploy_and_browser_startup_plan.md` (interpreted frontend is `~0.8 ms/char` linear;
   §0 of that plan). Until #21 lands, an AOT device build is blocked. The simulator lane (subprocess)
   is the honest interim ceiling.

> Note: `ios_runtime_aarch64_sim.bin` is ~31 MB (a full `simple` driver). A device build must not
> ship a spawnable driver; it ships a *linked library* exporting the two entry points above.

---

## 2. Packaging, signing, and release lanes

### 2a. Android (APK / AAB)

- Build: `cargo tauri android build --debug --target aarch64` → `app-universal-debug.apk`
  (`tauri_mobile_guide.md:170-172`). Release adds `--release` and a signed AAB for Play.
- SDK/NDK env (not on PATH by default): `ANDROID_HOME=~/Library/Android/sdk`,
  `NDK_HOME=$ANDROID_HOME/ndk/27.0.12077973` (`tauri_mobile_guide.md:161-165`).
- Tracked scaffolding: `gen/android/**` generated Kotlin (`WryActivity.kt`, `RustWebView*.kt`,
  `Ipc.kt`, `PermissionHelper.kt`), `tauri.build.gradle.kts`, `tauri.properties`,
  `tauri.settings.gradle`, `proguard-*.pro` (the 14 tracked files). Identifier `com.simple.ui`.
- **Signing (release):** upload key + Play App Signing; keystore path is an env/secret, never
  committed. `PermissionHelper.kt` is the runtime-permission surface (§4c).
- **Release lane:** debug APK for emulator smoke → signed release AAB for internal testing track →
  production track. Volatile `gen/android/**/build/` and `.gradle/` are gitignored
  (`.gitignore:239-241`) — never commit build output (it once bloated the WC to ~298k files, per the
  gitignore note).

### 2b. iOS (ipa / TestFlight)

- Simulator build (unsigned): the `gen/apple/project.yml` fixes at `tauri_mobile_guide.md:120-138`
  are **load-bearing** — swift-compat `OTHER_LDFLAGS` using `$(DEVELOPER_DIR)` +
  `$(PLATFORM_NAME)` (not the Metal cryptex `$(TOOLCHAIN_DIR)`, not a hardcoded
  `/iphonesimulator`), `ENABLE_DEBUG_DYLIB: NO`, and `CODE_SIGNING_*: NO`. **After any `project.yml`
  edit you MUST re-run `xcodegen generate` in `gen/apple/`** — `cargo tauri ios build` reuses the
  existing `.xcodeproj` and does not re-run xcodegen (`tauri_mobile_guide.md:114-118`).
- **Device / TestFlight (release):** flip `CODE_SIGNING_ALLOWED/REQUIRED` back on, set
  `DEVELOPMENT_TEAM`, provide a distribution provisioning profile, then archive → export `.ipa` →
  upload to TestFlight. Deployment target `iOS 14.0` (`tauri_simple_integration_status_2026-03-23.md:139-141`).
- **Entitlements:** the generated `gen/apple/` carries plist/entitlements; a device build that keeps
  the subprocess model would additionally need a JIT/`allow-unsigned-executable-memory` entitlement
  — which is exactly why §1b moves to static-link instead of requesting exotic entitlements.
- **ATS:** the webview loads assets over the secure `tauri://` scheme via
  `WebviewUrl::App("inline-shell.html")` — a plain `http://tauri.localhost` URL is rejected by iOS
  ATS (`NSURLErrorDomain -1022`, blank webview) (`tauri_mobile_guide.md:72-77`).

---

## 3. IPC / invoke architecture (webview ↔ Simple backend)

### 3a. Contract

The desktop and mobile-simulator lanes share one JSON protocol. Render output is an **IPC JSON
envelope** produced by `web_render_to_artifact(...).ipc_json` for `WEB_RENDER_TARGET_TAURI`
(`ui.tauri/backend.spl:40-52`, `ui.tauri/tauri_entry.spl`). Direction:

```
Simple → webview :  stdout line = IPC render envelope  (html + css + semantic snapshot)
webview → Simple :  DOM event → send_action → stdin line → parse_ipc_message → UIEvent
```

`TauriBackend.poll_event` reads a line from `rt_stdin_read_line()` and routes it through
`parse_ipc_message` (`ui.tauri/backend.spl:141-147`). The Render handler in the shell re-homes the
generated `<head><style>` into a persistent `<style>` because `innerHTML` drops `<head>`
(`tauri_mobile_guide.md:74-77`). **`eval OK` ≠ painted — verify pixels** (same anchor).

### 3b. The mobile IPC gap and the `app://` / back-channel requirement

- Historical: on mobile, **subprocess stdin/stdout is not always available**; the designed
  alternative is a WebSocket transport — `IpcTransport`/`StdioTransport`/`WebSocketTransport` in
  `src/app/ui.ipc/transport.spl`, **designed but not integrated into the shell's Rust side**
  (`tauri_simple_integration_status_2026-03-23.md:158-174`). The live source-bundle mode
  (`tauri_mobile_guide.md:41-81`) is the path that *did* get subprocess IPC working on the sim/emulator,
  so for the **simulator/emulator** the WebSocket transport is not on the critical path today.
- The **`invoke()` back-channel** (webview → native command return values) requires an `app://`
  (custom-protocol) build produced by `cargo-tauri build`, per project memory (2026-06-04). Plain
  `win.eval()` HTML injection is one-way; two-way `invoke()` needs the custom scheme. VERIFY before
  relying on it — the 2026-03-23 desktop doc shows `__TAURI_INTERNALS__.invoke()` working on desktop
  (`:74`), but the mobile back-channel proof is the item to re-establish.
- **Device (static-link) contract:** replace both stdio and WebSocket with **in-process FFI** — the
  shell calls `render_ipc()` / `send_action()` directly (§1b). This removes the transport question
  on device entirely.

### 3c. Internal-window / adaptive-nav integration

The mobile MDI proof already exercises a multi-window desktop-in-webview scene: the 2026-07-02
evidence records `windows=4`, taskbar `4/4`, window drag with `moved=true` and `drag_runtime=true`
(`tauri_mobile_renderer_parity_evidence_2026-07-02.md`). Internal windows / adaptive nav are rendered
by the **same** shared WM/HTML pipeline, not a mobile fork — consistent with "do not reinvent the
GUI." Where a WM/window-scene executor is involved, mobile stays a *consumer* of that scene via the
web render envelope; it never reaches a backend impl or `rt_*` directly (§5, isolation).

---

## 4. Input, lifecycle, and permissions

### 4a. Touch → event records

`TauriBackend.new_mobile/new_android/new_ios` set `touch_supported = true` and a `platform_hint`
(`mobile`/`android`/`ios`) (`ui.tauri/backend.spl:83-108`); `capabilities()` then adds
`Capability.Touch` (`:173-178`). DOM touch/click/input/key events arrive as IPC lines and become
`UIEvent`s via `parse_ipc_message` (§3a). The MDI proof confirms routed `body_click`, `body_input`,
`body_key`, and a positive `input_to_paint_ms` sample after routed input
(`tauri_mobile_guide.md:198-207`).

### 4b. Background / foreground lifecycle

Desktop-only window APIs (`title`, `inner_size`, `minimize`/`maximize`/`close`, `WindowControl`)
are `#[cfg(desktop)]`-gated and unavailable on mobile
(`tauri_simple_integration_status_2026-03-23.md:160-166`). Mobile lifecycle (suspend/resume,
webview visibility) must be handled by the shell's mobile entry (`tauri::mobile_entry_point` in
`lib.rs`, per the 03-23 file map) — **design item:** on background, pause the render loop / any
subprocess; on foreground, re-emit the last render envelope (the shared renderer is idempotent). No
current evidence that background/foreground is exercised — a gate in the plan.

### 4c. Permissions

- Android runtime permissions flow through generated `PermissionHelper.kt` (tracked). Declare only
  what the app uses; default UI showcase needs none beyond webview.
- iOS: usage-description plist keys per capability; none required for the pure-UI showcase.
- Tauri ACL: capability schemas live under `gen/*/schemas` / the tracked
  `tauri.conf.json`; plugins in use are `fs`, `dialog`, `notification` (seen in the shell's build
  fingerprints). `show_notification`/`show_dialog` are capability-gated in Simple
  (`ui.tauri/backend.spl:217-233`).

---

## 5. Responsive / adaptive layout — single source of truth

Breakpoints and device classification are shared with desktop, defined **once** in Simple:

| Concept | Definition | Anchor |
|---|---|---|
| Width size classes | Compact/Regular/Expanded via `default_breakpoints() = 600 / 840` | `common/ui/profile.spl:29-56` |
| Height size classes | `height_breakpoints() = 480 / 900` | `profile.spl:58-62` |
| Orientation | Landscape/Portrait/Square from w vs h | `profile.spl:16-27,72-79` |
| Device class | Phone/Tablet/Desktop; touch + shortest-side ≥ 600 → Tablet | `common/ui/form_factor.spl:29-84` |
| Touch target | 44 (Apple) / 48 (other touch) / 32 (desktop) px | `form_factor.spl:120-130` |
| Hover / density | hover desktop-only; spacing 8/12/8 | `form_factor.spl:132-147` |

The webview applies the size class from its **real device width** via `@media` CSS emitted by
`generate_css`, plus the `viewport-fit=cover` meta from `web_render_full_html`
(`tauri_mobile_guide.md:83-101`). App code that wants to branch the widget tree uses the same
`Breakpoints`/`SizeClass`/`LayoutProfile`/`ProfileResolver` (`profile.spl:216-266`) and
`FormFactorProfile` (`form_factor.spl:90-114`).

> **Discrepancy to reconcile (plan item).** The guide's prose (`tauri_mobile_guide.md:93-96`) states
> the *CSS* breakpoints as compact ≤600 / regular 601–1200 / expanded >1200, but the code's
> `default_breakpoints()` regular boundary is **840**, not 1200 (`profile.spl:56`). Either the CSS
> media queries diverge from the Simple size-class source of truth, or the guide is stale. Production
> requires one number — verify what `generate_css` actually emits and align the guide + code.

---

## 6. Performance / RSS targets + measurement protocol

**Honest current state:** no fresh cold-start / RSS numbers were measured for this design (doc-only
task). The parity evidence records *timing deltas from within the webview* (2026-07-02:
iOS `input_to_paint_ms≈461`, `delta_ms≈494`; Android `input_to_paint_ms≈30`, `delta_ms≈31`) — these
prove the JS timing plumbing works, **not** app cold start or memory. The large iOS numbers vs small
Android numbers are unexplained and must not be read as a device-perf comparison (different runs,
sim vs emulator).

**Targets to set and then measure (per device class):**

| Metric | How to measure | Proposed ceiling (to be validated) |
|---|---|---|
| Cold start → first frame | `am start` / `simctl launch` timestamp → first `[tauri-shell] render, html_len=` marker | Phone ≤ 2.0 s; Tablet ≤ 2.5 s (ASSUMPTION — set after baseline) |
| Steady RSS | `adb shell dumpsys meminfo com.simple.ui` / `xcrun simctl` + Instruments | Phone ≤ 250 MB; Tablet ≤ 350 MB (ASSUMPTION) |
| Input → paint | webview `input_to_paint_ms` after routed MDI input | ≤ 100 ms p95 |
| Bundle/app size | APK/ipa size; `ui_bundle.tar.gz` ≈ 8 MB today (`tauri_mobile_guide.md:50`) | Track, don't regress |

**Protocol:** capture on the real target host (macOS/iOS sim, Android emulator or device), three
cold starts, median reported, environment (device model, OS, GPU translation mode) recorded
alongside — mirroring the parity gate's "fresh evidence, retained ≠ pass" rule
(`tauri_mobile_guide.md:211-218`). Device AOT numbers (§1b) are the only ones that count as
"production iOS."

---

## 7. Evidence gates — what proves a lane works

Anchor: `scripts/check/check-tauri-mobile-renderer-parity-evidence.shs` and the per-lane validators
(`validate-tauri-ios-render-log-proof.js`, `validate-tauri-android-render-log-proof.js`,
`validate-tauri-mobile-mdi-proof.js`). A lane passes only with **all** of:

1. **Launch:** app foreground (`com.simple.ui`) on emulator/simulator (`tauri_mobile_guide.md:220-227`).
2. **Real render:** a `[tauri-shell] render, html_len=` marker (not a static card), plus a GPU
   context marker — **Metal** for iOS, **Vulkan** for Android (`tauri_mobile_guide.md:194-204`).
3. **Input:** MDI proof JSON with `*_event_status`, `*_capture_status`, `*_performance_status`,
   `*_interaction_latency_status`, `*_animation_status` all `pass`, persisted as
   `ios_mdi_proof.validation.env` / `android_mdi_proof.validation.env` (`tauri_mobile_guide.md:198-209`).
4. **Capture:** a nonblank screenshot with real dimensions/colors (2026-07-02: iOS 1206×2622,
   Android 1080×2400, colors 16).
5. **Desktop parity precondition:** the desktop production GUI/Web renderer parity evidence must pass
   *first* (`tauri_mobile_guide.md:182-189`).

**Skip ≠ pass. Retained ≠ pass.** The gate explicitly requires a rerun after renderer/shell/runtime/
browser-engine/SDK changes (`tauri_mobile_guide.md:210-218`). **No-fake-evidence rules already
burned in:** `eval OK ≠ painted` (verify pixels); `read_pixels` can silently fall back to software
(project memory 06-10); host/emulator Vulkan translation is **not** guest `skiavk` evidence — the
Pixel7 AVD still crashes `libhwui`/`VulkanManager` under guest `skiavk`/`swiftshader`/`lavapipe`,
so a green Android lane is recorded as *host-Vulkan* evidence only (`tauri_mobile_guide.md:228-230`).
**Device gates (new for production):** a real-device iOS smoke (§1b static-link build) and a real
Android device smoke — neither exists yet.

---

## 8. Update / versioning strategy for shipped apps

- **Shell + native runtime** ship as versioned store artifacts (Play AAB, App Store ipa). Bump the
  `com.simple.ui` version in `tauri.conf.json` / `tauri.properties` per release; store review is the
  update channel. No silent native self-update (both stores forbid shipping a spawnable interpreter
  that fetches+executes new native code — reinforces the §1b static-link direction on iOS).
- **UI content (`.ui.sdn` + Simple UI closure)** is embedded at build time (`ui_bundle.tar.gz` /
  static archive), so a UI change is a normal app release. If OTA UI updates are ever wanted, they
  must stay **data-only** (`.ui.sdn` + CSS), never shipping new executable code, to remain
  store-compliant — the renderer is in the signed binary; only the declarative scene is data.
- **Compatibility:** the IPC/render envelope is the version boundary. Keep
  `WEB_RENDER_TARGET_TAURI` envelope fields additive; the semantic snapshot
  (`semantic_ui_snapshot_*`) already carries a stage/status contract for forward-compat
  (`ui.tauri/backend.spl:11-18,162-166`).

---

## 9. Fit to the 3-facade backend-isolation architecture

Mobile must obey the same layering (`backend_isolation_architecture.md:21-83`): the mobile app names
an **engine on a facade** and never touches a backend impl or `rt_*`. Concretely:

- The Simple UI code renders via the **web pipeline** (`render_html_tree` → `generate_css` →
  `web_render_to_artifact`) — that is the `WebRenderer` facade's `pure_simple` engine path, whose
  core resolves down into Simple2D (`backend_isolation_architecture.md:66-68`). Mobile does **not**
  add a fourth facade.
- The webview (WKWebView / Android WebView) is the *presentation surface*, analogous to a backend
  impl's output — the app never calls it directly; it emits an envelope and the shell paints it.
- The isolation lint (plan P2, `backend_isolation_architecture.md:81-83`) greps `src/app/**` for
  App→backend-impl / App→`rt_*` edges. `src/app/ui.tauri/**` must stay clean of those edges;
  `TauriBackend` only imports `common.ui.*` / `app.ui.*` façade-level modules (verified against
  `backend.spl:7-36` — no `rt_*` except the one sanctioned `rt_stdin_read_line` extern for the IPC
  transport, which is the transport boundary, not a render backend).

---

## Appendix A — Verified anchors (2026-07-07, against `main` WC)

- `common/ui/profile.spl:50-62` breakpoints 600/840 + 480/900; `:29-40` SizeClass; `:216-266` ProfileResolver.
- `common/ui/form_factor.spl:68-84` `detect_device_class`; `:120-147` touch/hover/density policy.
- `src/app/ui.tauri/backend.spl:83-108` mobile/android/ios constructors; `:141-147` stdin IPC; `:206-209` device_class.
- `src/app/ui.tauri/tauri_entry.spl` minimal IPC entry.
- `doc/04_architecture/ui/rendering/backend_isolation_architecture.md:21-95` facades + matrix + perf anchors.
- `doc/07_guide/platform/mobile/tauri_mobile_guide.md` — live source-bundle (`:41-81`), iOS sim fixes (`:103-144`), Android (`:156-178`), evidence gate (`:180-230`).
- `doc/03_plan/compiler/self_hosted_frontend/full_cli_redeploy_and_browser_startup_plan.md` — Task #21 compiled-frontend (iOS-AOT dependency).
- On disk: `gen/android/app/src/main/jniLibs/arm64-v8a/libsimple_mobile_runtime_exec.so`; `src-tauri/ios_runtime_aarch64_sim.bin` (~31 MB, sim); `gen/apple/Externals/arm64/debug/libapp.a`.
- `.gitignore:225-241` gitignores `ui_bundle.tar.gz` + `ios_runtime_aarch64_sim.bin`.

## Appendix B — Failed / uncertain anchors (removed rather than guessed)

- **Shell Rust source (`src-tauri/src/*.rs`, `Cargo.toml`, `build.rs`, top-level `tauri.conf.json`,
  `dist/`, `scripts/build-ui-bundle.shs`)** — referenced by the dev guide but **not present** in the
  main WC and **not git-tracked** (only 14 `gen/**` files tracked). Treated as a Phase-0 recovery
  blocker, not cited as existing source.
- **`invoke()` mobile back-channel over `app://`** — asserted from project memory (2026-06-04); no
  in-repo mobile proof located. Marked VERIFY in §3b, not stated as fact.
- **CSS breakpoint 1200 vs code 840** — guide/code disagreement (§5); flagged for reconciliation
  rather than picking one.
- **Background/foreground lifecycle handling** — no evidence it is exercised; stated as a design item
  + gate, not as working.
</content>
</invoke>
