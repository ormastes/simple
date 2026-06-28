# GUI/Web/Mobile Renderer Hardening Resume Plan

## Recovered Objective

Resume the SPipe-driven hardening lane for Simple GUI and web rendering across
Chrome, Electron, Tauri2 iOS/WKWebView/Metal, and Tauri2 Android/WebView/Vulkan.
The lane must improve event handling evidence, rendering capture evidence,
performance evidence, animation evidence, coverage, system tests, docs, skills,
and GitHub synchronization without making false parity claims.

## Authoritative Workspace State

- Current workspace: `/Users/ormastes/simple`.
- Current branch: `codex/tauri-mobile-renderer-parity-2026-06-26`.
- Current branch head: `ad151553c2 feat: add tauri mobile renderer parity evidence`.
- Current branch upstream: `origin/codex/tauri-mobile-renderer-parity-2026-06-26`.
- Branch/upstream status at resume: `0 ahead, 0 behind`.
- `origin/main` has later crash-lane commits, including:
  - `810824dab0 test(gui): surface mobile interaction proof in parity report`
  - `6acc8b06b5 test(gui): surface metal render proof in report`
  - `7a1dc64ccd test(gui): report electron live smoke proof`
  - `ab7929448f test(rendering): surface electron gpu crash diagnostics`
- The old temp worktree `/tmp/simple-mobile-hardening` no longer exists.
- The current workspace is dirty. Treat existing dirty files as in-flight work;
  do not reset, overwrite, or fold them into unrelated cleanup without an
  explicit ownership decision.

## Existing Canonical Artifacts

- Feature requirements:
  `doc/02_requirements/feature/production_gui_web_renderer_parity_hardening.md`
- NFRs:
  `doc/02_requirements/nfr/production_gui_web_renderer_parity_hardening.md`
- Agent task history:
  `doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md`
- Architecture:
  `doc/04_architecture/ui/production_gui_web_renderer_parity_hardening.md`
- Design:
  `doc/05_design/ui/misc/production_gui_web_renderer_parity_hardening.md`
- Mobile parity spec:
  `test/03_system/gui/tauri_mobile_renderer_parity_evidence_spec.spl`
- Generated mobile parity manual:
  `doc/06_spec/test/03_system/gui/tauri_mobile_renderer_parity_evidence_spec.md`

## Resume Plan

1. Reconcile workspace ownership.
   - Separate current dirty branch work from unrelated generated/vendor/target
     churn.
   - Preserve user/other-agent changes.
   - Decide whether this branch should be rebased/merged onto `origin/main` or
     whether the crash-lane `main` commits should be cherry-picked into it.

2. Reconcile crash-lane commits.
   - Inspect the four known `origin/main` GUI evidence commits listed above.
   - Verify whether their scripts/spec expectations are already represented in
     this branch or need to be ported.
   - Avoid duplicate or contradictory evidence fields.

3. Validate the current dirty renderer/capture work.
   - Confirm direct environment/process access uses approved facades.
   - Confirm browser/file ops moved through owner modules after
     `browser_file_ops.spl` deletion.
   - Confirm updated RenderDoc, HTML/CSS manifest, widget fixture, and Chrome
     bitmap capture changes are real checks, not placeholder passes.

4. Close evidence gaps without false claims.
   - Chrome/Electron desktop evidence must report live capture provenance,
     viewport, format, mismatch count, artifacts, and tolerance policy.
   - iOS evidence must prove Tauri2/WKWebView layout plus Metal render-log
     markers.
   - Android evidence must prove Tauri2/WebView layout plus Vulkan render-log
     markers.
   - Divergent measured results are acceptable diagnostics only when reported as
     divergent, not as parity pass.

5. Run bounded verification.
   - Run each acceptance gate at most once per verify cycle.
   - Stop after three verify/fix cycles and report remaining failures instead
     of repeating green checks.

## Detailed Completion Criteria

Completion requires all of the following evidence in the current workspace:

- Requirements and NFR coverage:
  - REQ-001 through REQ-025 from the production GUI/Web renderer parity
    hardening requirement set are still traceable to implementation and tests.
  - NFR-001 exact parity claims use `mismatch_count=0`, `match=10000`, and
    `max_delta=0`.
  - NFR-002 forbids blur, tolerance, fake capture, and fixture fallback for
    exact parity claims.
  - NFR-006/NFR-007 diagnostic divergences include provenance and never pass as
    exact parity.

- Desktop capture evidence:
  - Chrome live capture evidence exists and distinguishes pass, divergent,
    fail, skip, and unavailable.
  - Electron live capture evidence exists and records native capture size,
    logical size, scale/downsample behavior, GPU/crash diagnostics, viewport,
    artifact paths, and mismatch data.
  - Retina/native-to-logical capture handling is verified where applicable.

- Mobile capture evidence:
  - `check-tauri-mobile-renderer-parity-evidence.shs` fails closed when the
    desktop source evidence is missing or failed.
  - iOS proof includes screenshot/layout evidence, Tauri2/WKWebView identity,
    and Metal markers from logs.
  - Android proof includes screenshot/layout evidence, Tauri2 Android WebView
    identity, and Vulkan markers from logcat or explicit GPU logs.
  - Missing iOS Metal or Android Vulkan markers produce fail reasons, not pass.

- Event and animation evidence:
  - Mobile interaction proof covers at least open-window or equivalent event
    routing markers and ties them to rendered state.
  - Animation/performance claims include captured frame or timing evidence, or
    are explicitly marked as not completed.

- SPipe and docs:
  - Executable specs live under `test/**`, not `doc/06_spec/**`.
  - Generated/manual spec docs under `doc/06_spec/**` match the executable
    specs.
  - The SPipe skill/docs no longer reference obsolete SStack behavior for this
    flow.

- Verification gates:
  - `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.
  - `sh scripts/audit/direct-env-runtime-guard.shs --working` passes.
  - `sh scripts/audit/direct-env-runtime-guard.shs --staged` passes when files
    are staged for commit.
  - Relevant focused SPipe specs pass once in the current session.
  - `git diff --check` passes.
  - Current branch is integrated with required `origin/main` GUI evidence
    commits or explicitly documents why it is intentionally separate.
  - Final pushed branch/ref is verified with `git ls-remote`.

## Non-Completion Signals

- A script accepts missing capture artifacts as parity.
- A tracked divergence is labeled as exact pass.
- A mobile proof has layout evidence but no Metal/Vulkan backend marker.
- Any executable `.spl` spec appears under `doc/06_spec`.
- Verification relies only on generated docs without running the executable
  spec or wrapper that owns the behavior.
- The branch ignores the later `origin/main` crash-lane evidence commits without
  an explicit reconciliation decision.
