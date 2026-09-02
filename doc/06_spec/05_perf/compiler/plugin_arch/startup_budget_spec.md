# Kernel Plugin Startup Budget

- Executable: `test/05_perf/compiler/plugin_arch/startup_budget_spec.spl`
- Requirements: `KPM-NFR-001`
- Evidence class: executable performance-contract definition; no measurement result is embedded.

## Scenario

- requires an explicit measured baseline and the normative less-than-2ms budget

## Freshness

This startup-delta contract is separate from the final RSS authority. RSS uses
an admitted per-architecture baseline, a 110% steady limit, and a 10% growth
limit across 20 warm requests. No runtime PASS is claimed.
