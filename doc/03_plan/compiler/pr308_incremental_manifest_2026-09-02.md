# PR 308 Incremental WIP Manifest

Base draft commit: `5ff63f9874c738de1aa618c133cd278aa6840497`

This update is intentionally WIP and unverified. Runtime validation is unavailable, and the deployment transaction test remains failing. Generated artifacts, binaries, caches, temporary files, user configuration, and unrelated concurrent changes are excluded.

## Included paths

- `doc/03_plan/compiler/pr308_incremental_manifest_2026-09-02.md`
- `scripts/bootstrap/bootstrap-deploy-transaction.shs`
- `scripts/bootstrap/bootstrap-from-scratch.sh`
- `scripts/bootstrap/rollback-bootstrap-deploy.shs`
- `scripts/bootstrap/verify-bootstrap-deploy-generation-authority.shs`
- `scripts/setup/release-platform.shs`
- `src/app/cli/_CliMain/main_and_help.spl`
- `src/app/compiler_entrypoint/admission.spl`
- `src/app/compiler_entrypoint/inventory_events.spl`
- `src/compiler/50.mir/_MirLowering/function_lowering.spl`
- `src/compiler/80.driver/cache/gc/fast_gc.spl`
- `src/compiler/80.driver/cache/package_archive_cache.spl`
- `src/compiler/80.driver/cache/package_index_route.spl`
- `src/compiler/80.driver/cache/package_scc_scheduler.spl`
- `src/compiler/80.driver/cache/package_tldr_metadata.spl`
- `src/compiler/80.driver/driver_source_pipeline_loading.spl`
- `src/lib/scv/compile_snapshot.spl`
- `src/lib/scv/compile_source_inventory.spl`
- `test/01_unit/app/compiler_inventory_event_call_chain_spec.spl`
- `test/01_unit/compiler/cache/host_shared_cache_gc_lifecycle_spec.spl`
- `test/01_unit/compiler/cache/package_archive_cache_spec.spl`
- `test/01_unit/compiler/cache/package_index_driver_cutover_contract_test.shs`
- `test/01_unit/compiler/cache/package_index_route_spec.spl`
- `test/01_unit/compiler/cache/package_scc_scheduler_spec.spl`
- `test/01_unit/compiler/cache/package_tldr_metadata_spec.spl`
- `test/01_unit/lib/scv/compile_source_inventory_spec.spl`
- `test/01_unit/scripts/bootstrap_deploy_transaction_test.shs`

## Known blockers

- The focused deployment transaction test exits nonzero and remains unverified.
- The admitted self-hosted CLI does not expose the required runtime `check` and `test` commands.
- Native bootstrap and qualification evidence remain pending.
