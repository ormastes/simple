# Tauri mobile shell source is untracked and absent from disk — app not reproducible from a clean checkout

- **Status:** RECOVERED (2026-07-07)
- **Priority:** P0
- **Date:** 2026-07-07
- **Area:** `tools/tauri-shell/` (Tauri 2 mobile shell — iOS + Android)
- **Severity:** Critical (the shipped mobile app cannot be rebuilt from `main`; all prior "verified" evidence is unreproducible)
- **Found while:** integrating the Tauri 2 mobile production design/plan docs and sanity-checking the P0.1 claim in `doc/03_plan/platform/mobile/tauri2_mobile_production_plan.md`.

## Recovery (2026-07-07)

Restored via `git checkout c8756fe7cc -- tools/tauri-shell` (last commit with the
complete tree before it was deleted 36 seconds later by `c8dbb4df4f`, per
`doc/09_report/tauri_shell_source_recovery_investigation_2026-07-07.md`). 132
files came back (118 previously-untracked + 14 already-tracked `gen/**`
scaffolding, unchanged).

**Correction to the investigation's Lane 3 finding:** the investigation
suspected the untracked sibling checkout `/Users/ormastes/simple-renderer-main`
(mtimes 2026-07-02) held *newer* MDI-proof fields/functions than git and that
git was missing the `libc::signal(SIGPIPE, SIG_IGN)` fix. Direct diff of both
sources after the restore shows the opposite: `c8756fe7cc`'s tree (git) is a
strict superset. It already contains every field/function the sibling has
(`event_sequence`, `device_pixel_ratio`, `screen_orientation`,
`source_window_count`, `has_simple_smoke_text`, `js_string_or_null`,
`mdi_proof_value`, the extended `build.rs` `string_include_line_with_file_default`
helpers) **and** the `libc::signal(SIGPIPE, SIG_IGN)` fix **and** the `libc = "0.2"`
`Cargo.toml`/`Cargo.lock` dependency entry that the sibling lacks. `main.rs` and
`app.rs` are byte-identical between the two sources; `tauri.conf.json` is
byte-identical. The sibling checkout is an older/abandoned snapshot (frozen
before several `test(gui): ...` MDI-proof commits landed on the git side on
2026-07-03), not a divergent-newer source. **No porting was needed or
performed** — the restored git tree was used as-is.

- **Build verify:** `cargo check` inside `tools/tauri-shell/src-tauri` (host
  target, macOS, default toolchain) compiles clean — 1 pre-existing `dead_code`
  warning (`simple_subprocess_args_for` unused) and 5 pre-existing
  `unused_unsafe` warnings in the vendored `tauri-runtime-wry-2.10.1` patch, no
  errors. Full `cargo tauri android/ios build` (mobile SDKs) was not
  attempted — out of scope for this bounded check.
- **Guard:** `git check-ignore -v` on all 5 previously-missing paths returns
  no match (exit 1) — confirmed never gitignored, consistent with the
  investigation. Added `tools/FILE.md` (declaring all `tools/*` depth-2
  entries, including `tools/tauri-shell`) and wired it into the root
  `FILE.md`'s `## Child Manifests` / new `## tools/` section, closing the
  `WRG002` gap for `tools/*` under `--strict` mode (the default non-strict
  guard already passed via grandfathering).
- **Restore commit:** see VCS log for
  `fix(mobile): restore tauri-shell source deleted by mislabeled c8dbb4df4f`.

## Summary

`git ls-files tools/tauri-shell` returns exactly **14 files**, and every one of
them is generated scaffolding under `gen/android/**` or `gen/apple/**`
(Gradle/Kotlin bindgen output + one `gen/android/.../assets/tauri.conf.json`
copy):

```
tools/tauri-shell/src-tauri/gen/android/app/proguard-tauri.pro
tools/tauri-shell/src-tauri/gen/android/app/src/main/assets/tauri.conf.json
tools/tauri-shell/src-tauri/gen/android/app/src/main/java/com/simple/ui/generated/Ipc.kt
tools/tauri-shell/src-tauri/gen/android/app/src/main/java/com/simple/ui/generated/Logger.kt
tools/tauri-shell/src-tauri/gen/android/app/src/main/java/com/simple/ui/generated/PermissionHelper.kt
tools/tauri-shell/src-tauri/gen/android/app/src/main/java/com/simple/ui/generated/RustWebChromeClient.kt
tools/tauri-shell/src-tauri/gen/android/app/src/main/java/com/simple/ui/generated/RustWebView.kt
tools/tauri-shell/src-tauri/gen/android/app/src/main/java/com/simple/ui/generated/RustWebViewClient.kt
tools/tauri-shell/src-tauri/gen/android/app/src/main/java/com/simple/ui/generated/TauriActivity.kt
tools/tauri-shell/src-tauri/gen/android/app/src/main/java/com/simple/ui/generated/WryActivity.kt
tools/tauri-shell/src-tauri/gen/android/app/src/main/java/com/simple/ui/generated/proguard-wry.pro
tools/tauri-shell/src-tauri/gen/android/app/tauri.build.gradle.kts
tools/tauri-shell/src-tauri/gen/android/app/tauri.properties
tools/tauri-shell/src-tauri/gen/android/tauri.settings.gradle
```

None of the **production shell source** referenced throughout
`doc/07_guide/platform/mobile/tauri_mobile_guide.md` is tracked:

- `tools/tauri-shell/src-tauri/src/{app,main,lib}.rs`
- `tools/tauri-shell/src-tauri/Cargo.toml`
- `tools/tauri-shell/src-tauri/build.rs`
- `tools/tauri-shell/src-tauri/tauri.conf.json` (top-level, not the `gen/android` copy)
- `tools/tauri-shell/dist/*.html` (`index.html`, `inline-shell.html`)
- `tools/tauri-shell/scripts/build-ui-bundle.shs`

This is not only a git-tracking gap — the files are **also absent from disk**
in the main working copy. The only things present under
`tools/tauri-shell/src-tauri/` besides the tracked `gen/**` scaffolding are
`target/` (build cache, correctly gitignored) and the two gitignored runtime
blobs. `.gitignore:225-241` only ignores build output and the packaged blobs
(`ui_bundle.tar.gz`, `ios_runtime_aarch64_sim.bin`) — it does not ignore the
source files, so their absence is not an intentional gitignore exclusion; the
source itself is simply missing.

**Consequence:** the mobile app documented in `tauri_mobile_guide.md` — and
exercised by the "verified" reports below — cannot be rebuilt starting from a
clean `git clone`/`jj` checkout of `main`. Every prior pass (2026-06-04 launch,
2026-06-06 Android live, 2026-05-30 iOS sim build) depended on shell source
that existed only in a developer's local working copy at the time and was
never committed.

## Evidence this worked before (now unreproducible)

- `doc/09_report/tauri_mobile_renderer_parity_evidence_2026-06-26.md`
- `doc/09_report/tauri_mobile_renderer_parity_evidence_2026-07-02.md`

Both reports describe real builds/runs against `tools/tauri-shell`, which
means the shell source existed on whatever machine/session produced them. It
is not recoverable from the current main WC or from git history at HEAD.

## Reproduction

```bash
git ls-files tools/tauri-shell             # 14 files, all gen/** scaffolding
ls tools/tauri-shell/src-tauri/src         # No such file or directory
ls tools/tauri-shell/src-tauri/Cargo.toml  # No such file or directory
ls tools/tauri-shell/dist                  # No such file or directory (or absent)
```

## Recovery directions

1. **Search for the source before reconstructing anything.** Check other
   machines/sessions/worktrees that may still hold the working copy that
   produced the 2026-06-26 / 2026-07-02 evidence reports: other jj workspaces
   (`jj workspace list`), `jj op log` / `git log --all --
   tools/tauri-shell/src-tauri/Cargo.toml` (in case it was committed and later
   removed by a rebase/restore), any local backup or CI artifact caches, and
   the build provenance of the two on-disk binary blobs
   (`ios_runtime_aarch64_sim.bin`, packaged `ui_bundle.tar.gz`) which may embed
   a build path or timestamp pointing at the source's last known location.
2. **If unrecoverable**, regenerate from scratch: `cargo tauri init` per
   `doc/07_guide/platform/mobile/tauri_mobile_guide.md`, reconciling the
   regenerated `src-tauri/{src,Cargo.toml,build.rs,tauri.conf.json}` and
   `dist/*.html` against the already-tracked `gen/android/**` output (IPC
   bridge shape, activity/WebView class names) so the two stay consistent,
   then re-run `scripts/build-ui-bundle.shs` (also needs to be recreated) to
   confirm the pipeline reproduces the packaged bundle.
3. Once source exists, **commit it as tracked** (not `target/`, not
   `*_bundle.tar.gz`, not `*_runtime_*.bin` — those stay gitignored) and re-run
   the full parity/evidence gate fresh, dated after the fix, before trusting
   any "verified" claim in the mobile docs again.
4. **Add a manifest/FILE.md guard** for `tools/tauri-shell/` (or extend
   `scripts/check-workspace-root-guard.shs`) that fails if
   `src-tauri/src/*.rs`, `src-tauri/Cargo.toml`, `src-tauri/build.rs`,
   `src-tauri/tauri.conf.json`, or `dist/*.html` are missing from
   `git ls-files`, so the shell source cannot silently go untracked again
   the way it did here.

## Related docs

- Design: `doc/05_design/platform/mobile/tauri2_mobile_production_design.md` §0a
- Plan: `doc/03_plan/platform/mobile/tauri2_mobile_production_plan.md` — Phase 0, P0.1 (blocks all
  later phases; P1 re-verification cannot run until this is fixed)
- Guide (documents the now-missing files as present): `doc/07_guide/platform/mobile/tauri_mobile_guide.md`
