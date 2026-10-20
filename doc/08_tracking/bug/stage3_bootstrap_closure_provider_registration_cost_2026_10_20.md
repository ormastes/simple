# Stage 3 bootstrap-fixed closure: per-module provider registration costs 12.8 s and RSS +28 MB per module

- Status: OPEN (measured on the r8 base; remeasure on release_phase3 tip)
- Date: 2026-10-20
- Platform: aarch64-unknown-linux-gnu
- Severity: P1 (Stage 3 closure loop ~4.6 h, projected RSS ~60 GB > 56 GB scope)

## Observation

Diagnostic Stage 3 (`s2diag17` relink, sha256 61f1f47a37bc..., tree
44a4b94ae95 = r8 base 630f773bdc7 + closure transient scope + providers
feed + #3925), SIMPLE_NATIVE_BUILD_THREADS=8, 56 GB scope. With closure
modules lowered against the full provider feed
(`stage3_bootstrap_closure_lowered_without_providers_2026_10_20.md`):

| closure module | heap_live | RSS |
|---|---|---|
| 50 | 4.12 GB | 25.0 GB |
| 100 | 4.51 GB | 26.3 GB |
| 150 | 4.92 GB | 27.8 GB |

- 12.8 s per module, flat (not growing): 4.7 modules/min, ~4.6 h for 1,318.
- `SIMPLE_MIR_SECTION_PROFILE_FILE`: `s4_promote_mir_registries` ->
  `s4_promote_fn_registries` is 167 ms per module, so #3925's promote is not
  the cost; the remaining ~12.7 s is `lower_module`'s provider registration,
  which walks every provider's traits, impls, structs (relocated layouts),
  functions, classes, enums and methods on every module.
- heap_live grows ~8.2 MB/module (linear); RSS grows ~28 MB/module.

## Expected on tip

release_phase3 carries the provider-walk perf chain this base lacks:
a92edd2fb7b (link table once per consumer), 6c15637b026 (provider session
index once, method rows on demand), db00168b079 (retire per-consumer
provider tables before promotion), cc601e8f3d3 / c4da3f8d8e4 (demand
provider layout and enum rows). 6c15637b026 does not cherry-pick onto the
r8 base. Remeasure the closure loop on a tip-based Stage 2 before treating
this as a live defect there.
