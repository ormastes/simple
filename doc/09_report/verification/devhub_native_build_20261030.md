# DevHub native build on current release, 2026-10-30

Status: FAIL; native executable absent, GUI launch NOT_RUN.

Luna executed the real full DevHub native build in `D:/dev/simple-devhub-integrate-20261030` against release base `4efdcb2a7c1d209e77d1d1ea06b095b380c7096e` plus frozen reviewed callback/cleanup changes. The explicitly supplied pinned Phase 2 producer was used with strict no-stub/no-bootstrap-delegate flags, the real headroom object and an isolated cache. No Stage 4 qualification is claimed.

Frozen staged patch SHA256: `5b3e206705fe55f71ee8df48b6a7aa2b3f97a150e01f1379dc862119263a9b12`.
Frozen unstaged patch SHA256: `967ed6127a427bc5a699ad02b0d315af51f1858fdf89cd6ac6a0e557c4b40d74`.
Both were revalidated unchanged after execution.

The compiler failed MIR lowering in two modules: 43 unsubstituted generic `T` errors and two unresolved `to_string` errors, including HTTP client `types.spl:57:23`. Internal interpreter exit was 1. The supervisor did not capture a numeric outer exit, so no outer exit is invented; compiler failure and absent output independently establish failure. Luna repaired that capture for a future changed-source run only.

Elapsed time: 233.59 seconds. Maximum sampled aggregate working set: approximately 3.82 GB, below the configured 8 GiB limit. No unchanged retry was started. Astra owns diagnosis of these compiler/library failures. The separately exhausted secured-database diagnostic remains open.

Retained evidence: `build/devhub-release-dev-20261030/build-manifest.sdn`, `build-observed-result.sdn`, `native-build.stdout.log`, `native-build.stderr.log`, and source patches in this worktree. No `devhub.exe` was produced, so browser/Electron behavior was not tested. The Windows browser-opener bug remains a source observation.

## Changed-source full-app run3

The encoder fixture passed, then the full app was rebuilt from the repaired source in `build/devhub-release-dev-20261030/full-app-run3/`. The to_string failure is absent. MIR now reports279 of280 modules successful, one failed, with43 generic-T occurrences across captured diagnostics. No executable exists. Although the outer compiler process returned0, its internal interpreter exited1 and MIR failed; the observed-result receipt correctly records FAIL_NO_EXECUTABLE. GUI launch remains NOT_RUN.

Run elapsed242.05s, peak sampled tree working set4,193,652,736 bytes. Both source patches remained frozen. The HIR mutex facade T warning from rt_hal/boundary is only a lead, not a proven failed-module attribution. No fourth full build or database diagnostic retry was started. See the retained observed-result receipt for exact hashes.

Completion audit: encoder repair has real native fixture evidence and removal of its full-build error. Database readiness, generic compiler repair, full native app construction, actual GUI launch, required broader verification and merged PR are incomplete. Requested release/dev is absent and the base-selection question remains unanswered. No STATUS: PASS or release claim is made.
