# Stage 3 two-pass HIR pool cannot be admitted: SCV roots omit src/plugins

- Date: 2026-11-13
- Status: fixed 2026-11-13 (branch work/stage3-scv-plugins-root-20261113)
- Area: native-build / bootstrap Stage 3 (`SIMPLE_FILE_WORKERS=0`, two-pass)
- Found by: Stage 3 go-to-end census (worktree simple-s3census-20261113)

## Symptom

On the Stage 3 two-pass route the capsule HIR shard pool is refused before
any worker starts:

```
[hir-shard] profile admission rejected: no closure request published
[capsule-shard] HIR warm-up failed (exit=1 failed_modules=0 reason=no closure request published); in-process build redoes HIR and reports it
```

so every Stage 3 with `SIMPLE_FILE_WORKERS=0` lowers HIR serially in process
(~50 min for the 1650-module bootstrap closure on aarch64).

## Root cause

The HIR worker profile admits a worker only against a published entry-closure
request (`native_build_closure_request_admit_v1`,
src/app/io/_CliCompile/native_build_closure_request_admit.spl:20), which is
tied to a published SCV authority. The Stage 3 block of
src/app/cli/bootstrap_main.spl never publishes either (the coordinator route
does, bootstrap_main.spl `bootstrap_coordinator_publish_authority_v1` +
`native_build_coordinator_prepublish_closure_v1`).

Publishing them there is not enough. Stage 3 passes exactly five `--source`
roots (k1 composition, cuda, src/compiler, src/app, src/lib; the exact
capsule refuses a sixth) and reaches `src/plugins` only through the entry
closure. `native_build_snapshot_source_roots_v1`
(src/app/io/_CliCompile/native_build_snapshot_roots.spl:4) preserves explicit
roots verbatim, so the SCV snapshot has no `src/plugins`. Tried on
2026-11-13 with an unadmitted Stage 2 built from the go-to-end branch:

```
error: focused native-build: unresolved import 'plugins.backend_vhdl.driver.driver_aot_vhdl_output' (used in .../build/scv/snapshots/scv-revision-v2-.../src/app/cli/bootstrap_backend_installer.spl)
[hir-shard] owner=0/2@0 status=BLOCKED exit=-1 claimed=0 sealed=-1 finished=false
[hir-shard] owner=0/2@0 reason: HIR worker cleanup deadline: HIR worker frozen retirement receipt invalid
[capsule-shard] HIR worker retirement unconfirmed (exit=1); in-process fallback blocked
```

## Fix direction

Publisher and consumer must reconstruct the same root cut, so the closure
namespaces the entry reaches (`src/plugins`, `src/os`) have to be added by
`native_build_selected_snapshot_source_roots_v1` for both sides, or the
Stage 3 argv contract has to carry them without a sixth capsule source slot.

## Workaround in use

The Stage 3 go-to-end census runs with `SIMPLE_HIR_SHARDING=0`: no HIR pool,
and each MIR shard worker lowers HIR itself (from the HIR cache when warm).

## Fix

`native_build_selected_snapshot_source_roots_v1` now adds `src/plugins` to an
explicit root cut that holds `src/app` when the checkout has `src/plugins`
(publisher and consumer both build their cut there), and the Stage 3 block of
`bootstrap_main.spl` publishes SCV authority + the closure request on the
go-to-end two-pass route. Pinned by
`test/01_unit/app/io/_CliCompile/native_build_positional_snapshot_spec.spl`
("selected snapshot roots of a Stage 3 explicit-root build"). The
`SIMPLE_HIR_SHARDING=0` workaround is no longer needed.
