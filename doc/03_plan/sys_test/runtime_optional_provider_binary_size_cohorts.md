# Runtime Optional-Provider Binary-Size Cohort Test Plan

## Scope

- Require an admitted pure-Simple Stage4 receipt; old seed results are diagnostic only.
- Compare release-small NoGC hello with a same-host, same-toolchain C hello.
- Compare checksum-equivalent Simple and Python interpreter startup and max RSS.
- Require empty collector/init and optional-provider load traces.
- Require 30 samples per lane for development and 100 for release.

## Static and Mutation Evidence

`test/01_unit/scripts/runtime_binary_size_startup_cohort_test.shs` proves the
clean evidence path and rejects collector retention, provider loading,
pre-Stage4/seed authority, insufficient samples, and binary drift without
running heavy cohorts.

## Native Evidence

`test/05_perf/compiler/runtime_optional_provider_binary_size_spec.spl` defines
the release-facing scenarios. A PASS requires retained Stage4-native cohort
receipts; unavailable or old-seed measurements remain BLOCKED/diagnostic.
