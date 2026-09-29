# Astra Vulkan async session implementation review

STATUS: WARN — source/injected-provider gates pass; hardware and admitted
Simple/provider integration remain unverified.

## Resolved source defects

- Split the 874-line owner into a 50-line dispatcher, six private implementation
  files, and a dependency-free protocol module; each is below 800 lines.
- Pin `Arc<Fence>` across the configured bounded wait without removing its
  registry entry. Polling and telemetry remain available to another thread.
- Add a bounded sequence window so a stalled prefix cannot accumulate unlimited
  out-of-order retirement records. Consume session fences without accumulating
  legacy fence tombstones.
- Check global handle allocation before wrap; reserve a fence identity before
  queue acceptance. Checked slot exhaustion clears resolved owners and closes
  admission rather than manufacturing an unknown live submission.
- Add explicit one-attempt idle recovery outside registries. Failed recovery
  retains resources. Explicit emergency abandonment retains the whole device
  generation in bounded process-lifetime quarantine and returns `QUARANTINED=2`.
  Reinitialization then requires process restart; no physical-release or
  automatic device-recreation claim is made.
- Add versioned frozen scalar telemetry, terminal snapshots, configurable
  pressure timeout, and host latency windows. GPU timestamps remain unavailable.
- Preserve provider ABI-v1 core requirements. Async revision 1 is optional and
  admitted only when its complete extension and supported query are present.

## Executed evidence

1. `cargo check -p simple-runtime --lib --features vulkan --offline` passed
   both focused compile cycles (9.42s and 8.81s). Final log:
   `/tmp/simple-vulkan-astra-check-2.log`. Only the pre-existing winit deprecation
   warning remains. No further provider build was launched.
2. Native tests of the exact production `vulkan_async_protocol.rs`: 14/14 PASS.
   Cover capacity 3/8/16, live-state bounds, command-four reuse, stale identities,
   sequence/generation limits, bounded deterministic receipts and latency windows.
3. Exact production owner modules with an injected Vulkan boundary: 9/9 PASS.
   Cover pending/timeout retention, one-time buffer/command release, rejected and
   ambiguous submission, fence-allocation failure, cancellation, stale snapshots,
   explicit recovery and failed-recovery quarantine. The concurrency oracle was
   strengthened and its single case passed again: both polls and the snapshot
   must finish within 200ms while a one-second fence wait is still pending.
4. Actual C loader compiled and linked fixture: PASS for legacy-v1 core,
   missing/partial/full async extension and preserved missing-core rejection.
   Final header/fixture strict C11 syntax check passed.
5. Scoped `git diff --check` passed. No admitted Simple spec execution,
   hardware benchmark, Chrome build, commit or push was performed by this lane.

## Remaining acceptance gates

Current-source admitted Simple execution and manual generation; real provider
link/export admission; live 3/8/16 GPU capacity/recycle/fence contention matrix;
actual descriptor/pipeline/buffer mutation and release tests; device loss and
compositor recreation integration; branch coverage; and matched C/Simple
hardware performance and memory evidence. Injected-device behavior cannot
replace those gates.

ABI and telemetry semantics:
`doc/07_guide/platform/ffi/vulkan_async_session.md`.
Registered injected test:
`src/compiler_rust/runtime/tests/vulkan_async_session_injected.rs`.
