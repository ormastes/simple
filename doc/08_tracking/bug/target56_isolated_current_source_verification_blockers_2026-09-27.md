# Target 5/6 isolated current-source verification blockers (2026-09-27)

Worktree: `/home/yoon/dev/simple-target56-isolated`, branch
`codex/target56-isolated`, baseline `4283f704f3ba4558e98613490783be040af4d408`.
Producer: historical admitted pure-Simple Stage2 binary, SHA-256
`319c7bd2f4dc15a0209fc0f76b805ff27afeecb4a411f8ad68c743191f0103d9`.
Its admission receipt names a source snapshot no longer present.

1. A full CLI build with default settings reached mold and failed on missing
   runtime symbols (`rt_cranelift_*`, GPU providers, file-view helpers) and
   unresolved source names. Log:
   `build/mini_builds/target56_full_cli/build.log`.
2. A retry with the bootstrap script's Stage 4 environment, one-binary mode,
   plugin sources, and the admitted Stage2 runtime authority remained at
   `source_closure 704/1202` for more than nine minutes after reporting that
   point at 2.7 seconds. It used one CPU core and reached about 1.09 GiB RSS.
   It was terminated under the repository runaway guard, preserving the cache
   and `build/mini_builds/target56_full_cli/build-stage4.log`.
3. A focused check-worker native binary built, but direct semantic checking
   reported missing module surfaces for repository imports. Syntax mode then
   reported an invalid array handle and compiler/FFI ABI mismatch. Logs:
   `build/mini_builds/target56_check_worker/{check,syntax}.log`.
4. A focused bootstrap CLI built objects and reached mold, then failed because
   the historical runtime authority lacks current file-view, CPU, and related
   runtime symbols. It also reported undeclared `optimizationconfig_debug` in
   `src/compiler/80.driver/pipeline_fn.spl:87`. Log:
   `build/mini_builds/target56_bootstrap_cli/build.log`.
5. The SCV observed-event native probe compiled and correctly rejected an
   overflow before publication. Its positive follow-up returned
   `inventory-publication-failed:publish-encode-empty` from the historical
   Stage2 native path. Log and artifact:
   `build/mini_builds/scv_observed_events_native_probe/`.

The isolated source needs an ABI-matched current runtime authority and a
current-source pure-Simple compiler candidate before SPipe, full-check,
Stage4 size/startup cohorts, and native event-publication acceptance can be
qualified. Do not treat the historical Stage2 checks as a PASS.

## Follow-up

The isolated `pipeline_fn.spl` now passes the enum variants directly for its
debug and release defaults, matching the existing `optimizationconfig_debug`
and `optimizationconfig_speed` definitions. This removes those imported helper
calls from the focused CLI closure. The historical-runtime ABI gaps and the
current-source Stage4 admission gap remain. No fresh Stage4 build has qualified
this change; administrator privileges do not supply the missing runtime or
compiler artifact.
