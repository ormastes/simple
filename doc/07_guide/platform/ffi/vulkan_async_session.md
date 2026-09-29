# Vulkan async submission session: B/N2

The canonical Simple facade is
`std.gc_async_mut.gpu.engine2d.vulkan_async_submission.VulkanAsyncSubmissionSession`.
It owns copied tokens. The Rust provider owns command buffers, fences, resource
leases and generation checks. Provider ABI v1 remains unchanged; async session
revision 1 is an optional complete extension selected by
`rt_vulkan_async_session_supported() == 1`. An older or partial provider returns
unavailable for session construction while its existing core surface remains usable.

Initialize the device, then call `open_with_wait(capacity, timeout_ns)` with
capacity 3–16 and timeout 0–1,000,000,000 ns. Zero means poll-only pressure.
`open(capacity)` retains the 1 ms default. Only one session may be active per
device generation. On pressure, acquire polls the oldest submitted slot once
and performs at most one configured wait. It returns `WOULD_BLOCK` even if
completion was observed: only explicit retirement releases slot capacity.

Use `acquire → command → record/end → submit → poll → retire`. Reserve a fresh
token for each recording. The returned fence is runtime-owned; legacy wait,
destroy and device-idle entrypoints reject session fences/active sessions.
Polling and telemetry remain available while a pressure wait pins an `Arc<Fence>`
outside both registries. Retirement is serialized with ownership mutations.
The bounded sequence window prevents out-of-order retirement metadata growing
behind a stalled frame; visible receipts publish only a contiguous prefix.

`cancel` closes admission; it does not preempt the GPU. `close` discards
unsubmitted recordings and returns pending while accepted work is live.
An unknown completion remains `UNKNOWN`, retains its resources, and closes
admission. Explicit `recover` performs one device-idle attempt outside the
registries. Success releases session resources and allows ordinary close;
failure keeps all owners. Recovery never fabricates completion receipts for
ambiguous commands.

After failed recovery, the explicit emergency `abandon_device` operation returns
`QUARANTINED = 2`, revokes the entire device generation, and retains its complete
runtime state in one bounded process-lifetime quarantine. It does **not** mean
completion or physical release. Device reinitialization is rejected until
process restart; automatic loss/recreation needs additional provider integration
and concurrency evidence. Telemetry keeps the nonzero retained-owner state.

Managed range binding is currently an explicit unsupported capability. Query
`vulkan_async_session_bind_buffer_supported()` before calling the session's
`bind_buffer`; the canonical no-GC SFFI owner reports `false`, and a valid
binding request returns `VULKAN_ASYNC_BIND_UNSUPPORTED` without invoking a
native symbol or mutating descriptors/resources. Malformed scalar arguments
remain `VULKAN_ASYNC_BIND_INVALID`. The legacy unscoped
`vulkan_sffi_bind_buffer` operation is not a substitute for this checked
admission contract. The scoped `vulkan_sffi_async_session_bind_buffer` name is
retained for API compatibility, but its Pure Simple owner also returns invalid
or unsupported and performs no native call while the capability query is false.

## Engine2D context admission

`std.gc_async_mut.gpu.engine2d.vulkan_context_admission` is the Pure Simple
production gate for DrawIR async promotion. It accepts the live
`VulkanBackend` owned by `Engine2D` and inspects that retained context, but raw
session/device/framebuffer handles are never published as admitted identities.
A caller cannot pass a positive handle or session generation as proof.

Unavailable production paths return before DrawIR serialization, so the
synchronous frame loop does not gain a second composition pass. The separate
`vulkan_context_draw_ir_packet` helper exercises the actual bounded canonical
codec without granting submission authority; malformed candidates fail closed.

With the committed Pure Simple buffer-binding capability disabled, the gate
currently returns `managed-buffer-binding-unavailable` for an otherwise live
context. If that prerequisite becomes available while exact context binding
is still absent, it returns `provider-context-binding-unavailable`. The
`Engine2D` window-present consumer records the exact status, reason, zero
packet checksum, and `async_claim=false`, then keeps the existing synchronous
path. Buffer-binding support alone is not context admission, and the
synchronous positive present result is not an async receipt.

## Telemetry version 1

`telemetry()` copies 64 signed scalar words from one frozen snapshot. An empty
array means unavailable or a concurrently replaced snapshot, never zero work.
The C ABI exposes `snapshot(session)` and
`snapshot_word(session, snapshot_token, index)`; stale or invalid reads return
`-1`. There is one snapshot per active session and one terminal snapshot, so
telemetry storage is bounded. The Simple facade retains its terminal handle for
reading after close or forced quarantine.

| Word | Meaning |
|---|---|
| 0–2 | schema version 1, word count 64, monotonic process-clock ns |
| 3–6 | capacity, live slot owners, max live slots, admission open |
| 7–10 | attempted, accepted, rejected, ambiguous submits |
| 11–14 | polls: total, pending, complete, failed |
| 15–18 | bounded waits, backpressure, retirements, cancellation transitions |
| 19–20 | cumulative retained/released submission buffer-lease bytes |
| 21–23 | explicit idle attempts, successful idle recoveries, published sequence |
| 24 | GPU timestamp availability: 0 (no GPU timestamp claim) |
| 25–31 | quarantined, unknown slots, live submission lease bytes, wait budget ns, unknown transitions, quarantined device roots, peak submission lease bytes |
| 32–56 | five groups: offer/submit, poll, wait, retirement, frame; each contains lifetime count, last ns, lifetime total ns, rolling p50 ns, rolling p95 ns |
| 57–63 | reserved zero |

Percentiles cover the last 64 observations per metric; they are not whole-run
benchmark percentiles. Frame latency runs from acquisition to exact retirement.
Buffer bytes measure retained submission leases, so a buffer shared by two live
slots contributes to both declarations. They exclude driver-private allocations,
unsubmitted recording resources, image allocations, and unrelated resource maps;
they must not be labelled total device VRAM or total physical released memory.
Quarantine counts remain nonzero until process exit. Normal submit/poll/retire
must have zero explicit idle recoveries.

## Evidence boundaries

The exact production protocol module has device-free native tests covering
capacity 3/8/16, capacity reservation, recycling, stale identities, checked
exhaustion, bounded receipt publication and bounded telemetry. The C fixture
`test/01_unit/runtime/vulkan_async_provider_compatibility.c` includes the actual
loader and verifies legacy-v1/partial/full-extension behavior.

On macOS, run it with dead stripping so unrelated hosted-runtime adapters do
not become link dependencies:

```sh
cc -std=c11 -Wall -Wextra -Werror -ffunction-sections -fdata-sections \
  -I src/runtime test/01_unit/runtime/vulkan_async_provider_compatibility.c \
  -ldl -Wl,-dead_strip -o /tmp/vulkan-provider-compat
/tmp/vulkan-provider-compat
```

The injected test `src/compiler_rust/runtime/tests/vulkan_async_session_injected.rs`
compiles the actual runtime owner files against a deterministic device/fence
boundary. It exercises pending waits, concurrent polling/snapshots, unknown
completion, failed recovery, resource retention, rejected submission, cancellation,
and recycling. It is intentionally a standalone low-disk harness (its injected
crate aliases are not a normal `simple-runtime` Cargo target), run with:

```sh
rustc --edition=2021 --cfg 'feature="vulkan"' --test src/compiler_rust/runtime/tests/vulkan_async_session_injected.rs -o /tmp/simple-vulkan-async-injected-test
/tmp/simple-vulkan-async-injected-test --test-threads=1
```

Source checks and these tests do not establish device execution. Current-source
admitted Simple execution, Vulkan failure/resource-retention injection,
two-thread live-fence contention, provider linking, actual three-submit/fourth-
command recycling, production compositor integration, and matched C/Simple
performance evidence remain required acceptance gates.
