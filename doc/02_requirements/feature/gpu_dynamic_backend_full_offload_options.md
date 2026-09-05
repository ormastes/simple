<!-- codex-research -->
# GPU Dynamic Backend and Full Offload — Feature Options

Existing selected ProcessingIR, Draw IR, renderer, CUDA/Metal, and web/DB
requirements remain in force. Select one provider-interface option below.

## Option A — Versioned function table with owned sessions (recommended)

Description: replace the GPU-specific per-symbol admission surface with one
`GpuProviderAbiV1` entry returning a size/version/capability-checked function
table. Use opaque provider/session/resource/completion handles; keep trusted
first-party providers in-process; allow provider replacement between processes
without changing the Simple binary.

Pros:
- Atomic ABI negotiation and required-operation validation.
- One lifecycle and evidence model for ProcessingIR and Draw IR consumers.
- Best fit for asynchronous completion, typed errors, provenance, and future ABI
  extension without exporting language-specific layouts.

Cons:
- Requires adapting the existing per-symbol Vulkan/CUDA loader and checkers.
- In-process provider faults can still terminate the host.
- True same-process hot replacement needs quiescence and resource-lifetime work.

Effort: XL, approximately 25–45 implementation/test/doc files plus native-host
evidence.

## Option B — Harden the current per-symbol GPU ABI

Description: retain `rt_simple_gpu_provider_abi_version`, backend bits, and
required backend symbol lists; add session, completion, replacement, TOCTOU, and
shared-receipt contracts without consolidating operations into a function table.

Pros:
- Smallest change from current native Vulkan/CUDA implementation.
- Existing dynamic-load checker and runtime dispatch remain reusable.
- Earlier focused Linux delivery.

Cons:
- Compatibility is spread across many symbol names and backend-specific lists.
- Harder to negotiate optional capabilities and atomically bind one provider.
- More likely to preserve separate CUDA/Vulkan/Metal public plumbing.

Effort: L, approximately 15–30 implementation/test/doc files plus native-host
evidence.

## Option C — Process-isolated provider service

Description: place every GPU provider in a supervised worker process using a
versioned serialized request/receipt protocol and shared-memory batch transport.

Pros:
- Provider crash and untrusted-plugin isolation.
- Replacement and rollback do not mutate the host process.
- Clear resource quotas and timeout ownership.

Cons:
- IPC, shared-memory, synchronization, and copy overhead complicate rendering.
- Largest implementation and operational surface.
- Native handles and low-latency frame submission become harder.

Effort: XL+, approximately 40–70 implementation/test/doc files plus platform
supervision and performance work.

## Common required scope

Every option must preserve the selected shared IR boundaries; prove unchanged-
binary provider replacement, typed failure, submission/fence/device readback,
and CPU parity; connect real device execution to the selected Web/DB batches;
profile function/IR/backend/end-to-end lanes; and retain unavailable native rows
as blockers.

