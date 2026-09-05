<!-- codex-design -->
# Agent Tasks: MC/DC and HAL Runtime Hardening

## Shared contract frozen before lanes

Interfaces: `McdcPolicy`, `McdcDecisionId`, `McdcWitness`, `HalOperationTag`, `HalProvider`, `HalComparison`, `EnvAccessInstruction`, `ScenarioExclusion` plus the V1 wire types in the detail design.

Manual helpers: `step_configure_coverage_policy`, `step_execute_tagged_providers`, `step_extract_environment_instructions`, `step_execute_environment_instructions`, `step_validate_mcdc_witnesses`, `step_record_reasoned_exclusion`.

Setup/checkers: `setup_mcdc_fixture`, `setup_hal_provider_matrix`, `check_static_off_zero_overhead`, `check_dynamic_idle_budget`, `check_provider_equivalence`, `check_exclusion_reason`. Unimplemented helpers use `fail(...)`, never a passing placeholder.

## Parallel lanes

- Lane A: HIR manifests, stable IDs, Boolean DAG, semantics/assurance validation.
- Lane B: MIR correlated probes, preservation, backend-neutral lowering, interpreter parity.
- Lane C: noalloc sink/analyzer/merge and `std.mcdc` compatibility migration.
- Lane D: aspect catalog/pack cache/slot ordering/activation lifecycle.
- Lane E: shared HAL/provider/environment/exclusion wire contracts.
- Lane F: isolated provider parent/workers, comparator, I/O tagged adapters.
- Lane G: environment extractor/executors and current-host interaction fixtures.
- Lane H: R3 verifier/baseline/receipts and warning-to-error removal gate.
- Lane I: executable SSpec/manuals, sabotage, performance/allocation evidence.
- Lane J: guides, feature/layer expert wikis, generated manuals, bug records.

Lower-model sidecars may inventory callers, platform matrices, and documentation only. `/root` owns merge and conflict resolution. Final acceptance and generated-manual review require a normal/highest-capability Codex review after all lanes converge.

## Merge order

Contracts -> manifests/validation -> sinks/provider protocols -> compiler lowering -> loader activation -> adapters/executors -> specs/perf -> compatibility removal/docs. No lane may add a private runtime alias, loader, provider registry, environment access, or skip mechanism.

## Runtime-boundary decision

- `runtime_need`: ordered fixed-capacity coverage sink operations and process/provider transport primitives not already exposed safely.
- `facade_checked`: `std.mcdc`, HAL, counterpart evidence, env/process facades, aspect pack/slots/cache.
- `chosen_path`: reuse facades, add smallest owner facades, and fix compiler/runtime owner only where the compiled boundary is missing.
- `rejected_shortcuts`: per-spec raw `rt_*`, app-owned HAL, fixture-only bypass, backend field pokes, MC/DC-private dynloader, threads standing in for isolation, and generated-code workarounds.

