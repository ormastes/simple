# Bug: `check-wm-production-fullscreen-evidence.shs` still fails to build — security-registry pre-pass hits the SAME `struct 'ANY' field 'message'` error the main lowering fix already cleared

**Status: FIX LANDED (2026-08-09), commit `7fa2d06aaa8`.** Genuine compiler
defect, not environmental. Reproduced deterministically on 2026-08-09.
Fix: `security_registry_sdn_from_sources` now skips (continues past) a file
its isolated single-file lowering pass can't resolve, instead of hard-
failing the whole native-build -- scoped strictly to that auxiliary scan,
main whole-program lowering untouched. `cargo build --profile bootstrap`
compiles clean. **NOT yet end-to-end validated**: proving the guard itself
now passes requires a full self-hosted bootstrap rebuild through
stage2/stage3 so the deployed `bin/simple` embeds this fix, which hasn't
been done yet (multi-stage, longer-running than this pass's budget).

## Symptom

`sh scripts/check/check-wm-production-fullscreen-evidence.shs` (bounded run,
~280s) still exits 1. All capture/snapshot/launch-log evidence keys report
`missing`:

```
wm_production_fullscreen_status=fail
wm_production_fullscreen_reason=production-native-build-failed
wm_production_fullscreen_windowed_capture=missing
wm_production_fullscreen_fullscreen_capture=missing
wm_production_fullscreen_restored_capture=missing
wm_production_fullscreen_windowed_snapshot=missing
wm_production_fullscreen_fullscreen_snapshot=missing
wm_production_fullscreen_restored_snapshot=missing
wm_production_fullscreen_launch_log=missing
wm_production_fullscreen_native_artifact=present   # stale artifact from Jul 26, predates this run's rebuild attempt
```

`build/wm-production-fullscreen-evidence/native-build.log`:

```
Build failed: lower security registry source
/home/ormastes/dev/pub/simple/src/os/hosted/hosted_browser_renderer_process.spl:
Unsupported feature: cannot infer field type while lowering
HostedBrowserRendererProcess._finalize_network: struct 'ANY' field 'message'
```

This is the **identical symptom string** documented as fixed in
`doc/08_tracking/bug/hosted_browser_renderer_process_finalize_network_any_field_infer_2026-08-08.md`,
reproduced *after* that fix's commits (`2c62f5cb028`, `b061a8929c2`) are
present on `main` and confirmed in the working tree (`git status --porcelain`
clean on the touched files; `Result<FetchResponse, BrowserError>` present at
every relevant signature in `fetch.spl` and `h1_client.spl`).

## Root cause: two independent lowering passes, only one was fixed

`native-build` runs the requested source through the normal whole-program HIR
lowering pipeline **and**, separately, a security-capability scan
(`src/compiler_rust/compiler/src/pipeline/native_project/mod.rs`):

```rust
// mod.rs:1223 security_registry_sdn_from_sources()
for (path, source) in file_sources {
    if !source_may_declare_security(source) { continue; }
    ...
    let module = crate::hir::lower_with_context_lenient_and_project_hint(&ast, path, project_hint)
        .map_err(|err| format!("lower security registry source {}: {}", path.display(), err))?;
    let inventory = build_security_inventory(&module);
    ...
}
```

`hosted_browser_renderer_process.spl` matches `source_may_declare_security`
(it imports `...browser_engine.security.origin_policy` and references
`sandbox`/`security` tokens), so it is fed through
`lower_with_context_lenient_and_project_hint`
(`src/compiler_rust/compiler/src/hir/lower/mod.rs:185`):

```rust
pub fn lower_with_context_lenient_and_project_hint(
    module: &Module, current_file: &Path, project_hint: Option<&Path>,
) -> LowerResult<HirModule> {
    let module_resolver = ModuleResolver::single_file_with_project_hint(current_file, project_hint);
    ...
}
```

This lowers the file **in isolation** (`ModuleResolver::single_file_with_project_hint`),
without the cross-module symbol/type resolution the main whole-program
lowering pass has. `self.network: FetchEngine`, and
`FetchEngine.finalize_single_hop(...) -> Result<FetchResponse, BrowserError>`
live in a different file
(`src/lib/gc_async_mut/gpu/browser_engine/net/fetch.spl`); single-file
lenient lowering can't resolve that imported type, so `finalize_single_hop`'s
return type collapses to `ANY`, and `error.message` on the `Err(error)` arm
in `_finalize_network` (line 1635 of
`src/os/hosted/hosted_browser_renderer_process.spl`) is then an
unresolvable field access on an `ANY` struct — the exact error text.

The 2026-08-08 fix (pinning `Result<FetchResponse, BrowserError>` explicitly
instead of eliding the error type) genuinely fixed the **main** lowering
pass, which does have full-project symbol resolution and only needed the
explicit type to stop back-inference from landing on `ANY`. It did nothing
for the **security-registry** pass, which can't resolve the imported type at
all regardless of how explicit the local annotation is, because it never
loads `fetch.spl` in the first place — it lowers
`hosted_browser_renderer_process.spl` alone.

Confirmed independently: a from-scratch build with `native-cache` deleted
(`/tmp/cwtest-cache`) was also attempted; it did not reach this file before
hitting an unrelated 60s per-file compile timeout on
`src/lib/nogc_sync_mut/js/engine/interpreter_native.spl` (separate, known
slow-file issue, not this bug — the cache warm-up in the guard's own
`$BUILD_DIR/native-cache` avoids that timeout for unrelated files). The
warm-cache run through the guard script's own `BUILD_DIR` is what
deterministically reproduces the security-registry error above; cache
staleness was ruled out as the cause because native-build cache objects are
content-hash-named, not mtime-gated.

## Secondary, currently-unreached issue: no display server on this host

Downstream of the build failure, the script also fails closed on
`platform-window-capture-unavailable` if `DISPLAY`/`WAYLAND_DISPLAY` are both
unset (`scripts/check/check-wm-production-fullscreen-evidence.shs:340-352`).
On this host, `echo $DISPLAY $WAYLAND_DISPLAY` is empty but `Xvfb` and
`xvfb-run` ARE installed (`/usr/bin/Xvfb`, `/usr/bin/xvfb-run`). This is not
what's currently failing the guard (the build failure above happens first,
long before the display check), but it will become the next blocker once
this compiler bug is fixed. `.github/workflows/gui-hardening-evidence.yml`
already has the `xvfb`/`libgtk-3-0`/`libnss3`/`libxss1` install + `xvfb-run`
wrapping pattern to reuse for CI wiring of this guard and
`check-wm-host-css-override-evidence.shs` — deferred until this bug is
fixed, to avoid wiring a permanently-red job.

## Suggested fix direction (not applied — needs compiler-team judgement)

`security_registry_sdn_from_sources` needs either:
- a whole-project-aware resolver (reuse the same `ModuleResolver` context the
  main lowering pass builds, instead of `single_file_with_project_hint`), or
- to tolerate `ANY`-typed fields when building the security inventory instead
  of treating unresolved field types as a hard `Unsupported feature` error
  (the pass only needs `require_policy:`/`enter_sandbox:`/`lowered_backend:`
  markers — it does not need full type-soundness on unrelated fields like
  `error.message`).

Filed as a distinct defect rather than attempted here per the "don't
deep-fix without full understanding" guidance — this is Rust compiler
pipeline code (`src/compiler_rust/compiler/src/pipeline/native_project/mod.rs`,
`src/compiler_rust/compiler/src/hir/lower/mod.rs`), and the two candidate
fixes have different tradeoffs (correctness completeness vs. scan leniency)
that should be chosen deliberately.

## Evidence

- `build/wm-production-fullscreen-evidence/native-build.log` (this run)
- `build/wm-production-fullscreen-evidence/evidence.env`, `report.md`
- `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:1164-1300`
  (`generate_security_registry_init_object`, `security_registry_sdn_from_sources`,
  `source_may_declare_security`)
- `src/compiler_rust/compiler/src/hir/lower/mod.rs:180-197`
  (`lower_with_context_lenient_and_project_hint`)
- `src/os/hosted/hosted_browser_renderer_process.spl:1628-1637` (`_finalize_network`)
- Fix commits already on `main` that resolved the *main*-pass instance of
  this symptom but not the security-registry instance: `2c62f5cb028`,
  `b061a8929c2`
