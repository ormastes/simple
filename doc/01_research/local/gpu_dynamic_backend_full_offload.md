<!-- codex-research -->
# GPU Dynamic Backend and Full Offload — Local Research

## Scope and reviewed lanes

This umbrella research reconciles the existing GPU processing, Engine2D/Draw IR,
GUI/Web/WM, CUDA/Metal, and GPU web/database lanes. Existing selected requirements
remain authoritative; this document records integration gaps rather than replacing
their research.

## Dynamic provider boundary

- Native host loading exists through `src/os/posix/host_dynlib_sffi.spl` and
  `src/os/posix/dynlib.spl`. The C implementations currently exist in both
  `src/runtime/runtime_dynload.c` and `src/runtime/runtime_native.c`, leaving a
  duplicate-owner/link-winner risk.
- A stable generic provider wire already exists in
  `src/lib/nogc_sync_mut/composition/provider_contract.spl` and
  `src/os/smf/provider_query_wire.spl`: fixed-size little-endian request/result
  records, opaque handles, digests, and explicit status.
- The current GPU loader uses a different per-symbol ABI. The focused checker
  `scripts/check/check-gpu-provider-dynload-registry.shs` proves native Vulkan
  and CUDA library loading, ABI/backend-bit rejection, required-symbol rejection,
  handle-local resolution, provenance, dispatched scalar/buffer operations, and
  absence of a static provider dependency.
- `src/os/smf/provider_loader.spl` admits registry evidence but does not map the
  SMF image into process-callable memory. The stable provider registry therefore
  correctly reports native/SMF query bridges unavailable until a callable owned
  session exists.
- Provider admission hashes only before open. Existing TOCTOU specs require a
  post-open digest comparison and `PROVIDER_ADMISSION_DIGEST_UNSTABLE`, but the
  loader does not implement that check.
- Generation/reload support in `src/os/smf/dynsmf_session.spl` is synthetic at
  the provider boundary; it is not evidence that a running Simple process safely
  replaces an executable GPU provider. Provider replacement between separate
  unchanged-binary processes is the first honest deliverable; in-process hot
  replacement needs explicit session quiescence and lifetime ownership.

## Shared IR and rendering routes

- `src/lib/common/processing/processing_ir.spl` is the shared compute model, but
  currently supports only `FILL_U32` and `FILL_RECT_U32`.
- Real Vulkan `FILL_U32` submit/readback exists in
  `src/lib/gc_async_mut/processing/vulkan_fill_u32.spl`; the production Web to
  Engine2D Vulkan test also proves exact device readback for its selected route.
- `src/lib/gc_async_mut/processing/backend_pipeline.spl` does not compile general
  ProcessingIR. It selects precompiled Vulkan blobs, mislabels the non-Vulkan
  fallthrough as HLSL, and reports compiler/validator failure fields
  unconditionally. Its host probe returns a target name rather than probing a
  compiler, runtime, or device.
- Web production presentation directly calls Engine2D draw operations rather
  than lowering through ProcessingIR. Normal GUI, WM, and Web hosts still use
  CPU/raster/HTML routes; only the focused 2D Vulkan host uses strict Draw IR to
  Engine2D to Vulkan.
- DrawIrComposition and ProcessingIR are distinct contracts. The correct
  integration is shared provider/session/evidence ownership below both IRs, not
  pretending that Draw IR is already ProcessingIR or inventing another public IR.

## CUDA and Metal

- CUDA ProcessingIR has a real driver/readback path in
  `src/lib/gc_async_mut/processing/cuda_fill_u32.spl`, but it embeds a fixed PTX
  program and supports only `FILL_U32`; native source-matched evidence remains
  open. Engine2D has separate CUDA drawing kernels.
- Metal has deterministic MSL generation, an explicit emulator evidence class,
  and conditionally compiled native execution. Linux cannot prove the native row;
  the prepared macOS TODO remains a completion blocker.
- Existing final requirements already select shared ProcessingIR, CPU oracle,
  deterministic backend artifacts, exact device provenance, and no backend API
  fork. These choices are not reopened.

## Web and database offload

- The selected requirements in `doc/02_requirements/feature/gpu_web_db_offload.md`
  retain CPU ownership of networking, durability, and invalidation and select
  bounded coarse-grained GPU batches for RAM, SSD, NoSQL, and vector workloads.
- Reverse-proxy policy/state helpers exist, but the worker does not register or
  run the proxy. An unregistered proxy handler returns 501; streaming, upgrade,
  and integration/performance evidence remain open.
- `src/lib/nogc_sync_mut/web_db_offload/device_backend.spl` accepts a caller-
  supplied `native_device_execution` flag and timing. It performs no kernel
  launch, fence, readback, checksum, or device receipt verification.
- Web and DB paths compare externally supplied GPU candidates with CPU outputs.
  They do not yet execute scans, filters, joins, ANN, transforms, or web payload
  work through ProcessingIR. Existing specs prove decision/fallback contracts,
  not device computation.
- The DB SIMD path truthfully reports scalar fallback. The current performance
  report is WARN, and planned proxy/DB/native performance specs are absent.

## Profiling implications

Evidence must separately measure producer/function-call cost, IR construction
and bytes, backend marshalling, host submit, queue/fence wait, device execution,
readback, and end-to-end latency. A host timer around an asynchronous submit is
not device time. Profiles must bind workload, binary/provider hashes, device
identity, warmups, samples, median/p95, throughput, and max RSS.

## Decisions already selected

- Small static core plus versioned dynamic providers.
- ProcessingIR and DrawIrComposition remain canonical shared contracts.
- CPU oracle and fail-closed typed fallback/unavailable evidence.
- Reliability-first web/DB offload with CPU-owned protocol and durability paths.
- Native Metal evidence remains blocked rather than emulated as PASS.

## Genuinely unresolved decisions

1. Whether GPU ABI v1 remains a validated per-symbol surface or moves to one
   versioned function table with explicit session/completion ownership.
2. Whether untrusted third-party providers are in-process or process-isolated.
3. Numeric promotion thresholds for IR overhead, rendering, web, and DB profiles.

## Cooperative review

Lower-model sidecars reviewed dynamic loading, rendering, web/DB, and existing
documents. This normal-capability merge reconciled their contradictions. Final
requirements and done marks still require highest-capability review.

