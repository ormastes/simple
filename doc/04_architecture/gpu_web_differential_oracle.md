<!-- codex-architecture -->
# GPU/Web Differential Oracle Architecture

## Status

Proposed shared test infrastructure.  It is intentionally independent of the
SimpleOS Venus production implementation and may be adopted by browser/web
renderer tests incrementally.

## Decision

Use a two-capsule MDSOC boundary:

```text
Pure-Simple production layer              Test-only conformance capsule
--------------------------------------    ---------------------------------
common.spec.differential_trace            std.test.differential_conformance
 TraceEvent / NormalizedTrace               TraceComparator policy/result
 injected trace sink only                   GpuEnvironmentProfile
 no SFFI, no reference dependency           ReferenceOracleAdapter descriptor
                |                                      |
                +---- normalized values only ----------+
                                                       |
                                  no-GC SFFI oracle owner (future)
                                  std.gpu.reference_oracle_sffi
                                  Mesa/Vulkan or Chromium adapter
```

`common` owns the immutable cross-layer schema.  Venus transport/protocol/
queue/fence/readback and Web style/layout/paint/composite may emit it through a
test-injected sink, but neither imports the comparator, another renderer, or a
foreign provider. `std.test` owns semantic projection and comparison. This
keeps the value contract reusable while making test-oracle dependency one-way.

### Frozen schema and layer IDs

`TraceEvent` contains only `schema_version`, run/run-relative sequence and
monotonic time, `layer_id`, operation, opaque *normalized* object/parent IDs,
result/error classes, digest/scalar facts, and an environment profile ID.
`NormalizedTrace` additionally records canonical UI profile ID, architecture,
transport, enabled features, Venus/device/oracle identities, device-origin
readback/fallback facts, `dropped_events`, and `complete`. It
must never contain raw address, native handle, wall-clock timestamp, or mutable
payload. Schema v1 layer IDs are:

- `virtio_transport`, `venus_protocol`, `vulkan_api`, `draw_ir`
- `web_layout`, `web_paint`

SimpleOS handshake order is bounded `virtio_transport:discover` ->
`venus_protocol:handshake` -> `vulkan_api:submit` -> `vulkan_api:fence` ->
`vulkan_api:device_readback`. This aligns with the existing frozen production
types: `VirtioGpuDiscoveryProvider`, `VenusProtocolProbe`, `VenusSession`,
`VenusCommandQueue`, `VenusFenceReceipt`, and `VenusDeviceReadbackReceipt`.

### Semantic comparison, not raw wire equality

The comparator checks ordered state transitions, result/error class,
operation-specific digest/scalar facts, and mapped object lineage. An adapter
provides parallel candidate/reference ID maps for legitimate handle or protocol
translation. Per-trace monotonic timestamps prove local event order but are not
compared for equality across providers. It does *not* accept raw byte equality as proof: Vulkan/Venus
serialization, driver allocation, and Chromium display-list/layerization may
transform bytes while preserving the required semantics. Pixel readback is a
separate exact digest/scalar observation in the relevant trace event.

Every layer test must have: (1) a known-good semantic fixture; (2) at least one
mutation that changes a layer/op, capability, mapped lineage, result/error,
barrier/fence, or pixel digest and is rejected; and (3) malformed/order/budget
negative coverage. A comparison that accepts a mutation is a failing oracle,
not a skip.

### Dynamic reference oracle boundary

The future only approved foreign boundary is
`src/lib/nogc_sync_mut/gpu/reference_oracle_sffi.spl`, owned by the canonical
no-GC sync backend. It must use the existing `std.sffi.dynamic` loading
primitive and expose safe test-only calls after all of these checks:

1. explicit library path/identity, ABI version, and required symbol list;
2. symbol existence before call, expected function ABI/signature, and loader
   error copied into a bounded Simple error value;
3. opaque-handle ownership/release and no handle escape into trace values;
4. compile/JIT ABI probes and unavailable-provider negative tests.

`test/helpers/gpu_reference_oracle.spl` and a matching web/Chrome adapter may
then normalize reference observations. No upstream Mesa, virglrenderer,
Vulkan-Loader, Chromium, or VUDA source is copied; no such library is linked or
loaded by the production driver.

Khronos documents that the loader mediates application/layer/driver dispatch
and obtains functions through query interfaces, so an oracle must validate its
symbols rather than assume direct exported entry points. Mesa documents Venus
as Vulkan command serialization over virtio-gpu and lists the guest feature
requirements, which become profile facts rather than silently assumed host
conditions. Chromium RenderingNG similarly exposes separable style/layout,
pre-paint, paint, compositing/layerization, and raster stages; browser tests map
those semantics to `web_layout`/`web_paint` projections rather than compare a
GPU command stream. Sources: [Khronos loader architecture](https://github.com/KhronosGroup/Vulkan-Loader/blob/main/docs/LoaderInterfaceArchitecture.md), [Mesa Venus](https://docs.mesa3d.org/drivers/venus.html), [Chromium RenderingNG](https://developer.chrome.com/docs/chromium/renderingng-architecture).

## Environment and performance profiles

`GpuEnvironmentProfile` is an admission policy, not proof. It binds a named
profile to canonical UI profile ID, expected architecture/transport, required
feature conjunction, Venus/device/oracle identities, no-fallback and
device-origin-readback expectations. It also requires operations such as
discovery/handshake/submit/fence/readback and can bound trace event count and
run-relative elapsed time. `complete=false` or `dropped_events>0` is rejected
before any comparison. Initial profiles:

| Profile | Required facts | Admission proof |
|---|---|---|
| `simpleos-qemu-x86_64-vulkan-virtio` | `virtio-gpu-pci`; 3D/capset/resource-blob/host-visible/context-init; Venus capset; queue/fence/readback | normalized `virtio-gpu` + `mesa-vulkan-oracle` identity; exact device-origin pixels; no CPU fallback |
| `simpleos-qemu-aarch64-vulkan-virtio` | `virtio-gpu-mmio`; same required feature conjunction | same device/oracle/readback/fallback evidence |
| `simpleos-qemu-riscv64-vulkan-virtio` | `virtio-gpu-mmio`; same required feature conjunction | same device/oracle/readback/fallback evidence |
| `host-vulkan-oracle` | loader ABI/symbols, selected ICD, queue/extension facts | independent reference readback and normalized trace |
| `chrome-web-oracle` | browser build/viewport/fixture and renderer-stage capture | semantic layout/paint trace plus reviewed exact bitmap artifact |

Initial unit profile bounds are <=16 events and <=1 microsecond of normalized
fixture time. Live test budgets must be profile-specific and reported as p50,
p95, maximum trace event count, reference adapter initialization time, and
readback latency. Discovery happens once per test session; no per-event shell
out, full-tree scan, or repeated dynamic loading is permitted.

## VUDA decision

Repository audit found no `VUDA`, `Vuda`, or `vuda` identifier in owned source,
tests, architecture/design/plans (vendor and archive paths excluded). External
VUDA is a header-only CUDA-runtime-like API layered over Vulkan, not a Venus
transport or Vulkan ICD. Therefore: **do not migrate or introduce VUDA**. Keep
the pure-Simple Vulkan/Venus API as the production surface. Revisit only if a
separately approved CUDA-compatibility feature has concrete Simple callers;
then compare it as a test-only adapter against the same trace schema, never as
a driver dependency. Reference: [Vulkanized compute survey](https://vulkan.org/user/pages/09.events/vulkanised-2023/vulkanised_2023_transitioning_to_vulkan_for_compute.pdf).

## MDSOC consequences

- Positive: one schema enables layer-local comparison for Venus and browser
  rendering without a shared renderer or test-only dependency in production.
- Negative: adapters must explicitly construct semantic facts; generic byte
  replay is deliberately insufficient.
- Neutral: existing bitmap/golden scripts continue to produce artifacts; they
  gain no automatic semantic equality claim until wrapped by an adapter.
