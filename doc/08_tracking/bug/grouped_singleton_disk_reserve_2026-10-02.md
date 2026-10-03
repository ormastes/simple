# Singleton native group admission consumes its disk reserve

Status: concrete source defect repaired in a draft candidate; executable
qualification pending. Base `c3ca42257a719feb4372cdf44290178e7510434a`.

`src/app/bootstrap_builder/grouped_native_run.spl::native_group_capacity_check_v1`
used `max(source_bytes * 8 + estimated_group_disk_bytes, minimum_free_disk_bytes)`.
Both wave checks instead require reserve plus active growth plus candidate
growth. With no source bytes, an 8.5 GiB reserve and 2 GiB estimate, the singleton
admitted 8.5 GiB even though only 6.5 GiB would remain after estimated growth.
The same contract requires 10.5 GiB; one byte less must refuse.

The shared pure requirement helper `native_group_disk_required_v1` now computes
reserve + active growth + 8x source bytes + estimated candidate growth.
`native_group_disk_budget_v1` validates observed capacity and returns the actual
admission decision plus its requirement; singleton and both wave decisions use
this owner. Singleton checks pass zero active growth. Active-growth accumulation
uses the checked requirement helper with zero reserve, so valid wave requirements
remain unchanged. Every negative input and
each multiplication/addition overflow is rejected before the unsafe arithmetic.
The existing public run/source validators retain their tighter practical bounds.

This changes no memory/commit cap, queue order, retry policy, inventory, backend,
cache identity, probe count or host-access mechanism. It adds constant-time
arithmetic checks without extra I/O. It does not implement broader manager or
platform features and is unrelated to the exhausted parser-probe cycle limit.

Focused cases are added to the existing
`test/01_unit/lib/common/build_manager/grouped_native_process_policy_spec.spl`
and its mirrored manual. They cover both observed and source-amplified capacity
gaps, equality/one-byte-below, active growth, zero, negative inputs, overflow at
every arithmetic step, and exact i64 maximum values.

No admitted lightweight self-hosted test runner was identified. Native/SSpec and
required core/MCP checks remain UNRUN; no Rust fallback or bootstrap build was
launched. The Windows c829 diagnostic producer passed hello but its manager
image build failed parsing and is not treated as an admitted general test runner.

Prior source evidence:
`D:/dev/capacity-admission-verification-20261002/full-grouped-queue-admission-handoff.md`.
