# GPU Scheduler Hardening and GPU-Resident Rendering Detail Design

## First implementation slice

Add deferred DrawIR submission using the present bounded runtime queue:

1. Build bounded routing metadata and submit exactly once; this first increment
   does not yet register a packed DrawIR payload.
2. Return `Engine2dDrawIrDeferredReceipt` with submission provenance and no
   drain/dispatch result.
3. Later call the explicit completion helper with a bounded packet count.
4. Drain and validate through the existing backend/payload checks.

No API may spin, wait, or call a CPU renderer as a hidden fallback. The
existing immediate `engine2d_draw_ir_runtime_queue_dispatch` is unchanged so
callers migrate deliberately.

## Deferred payload boundary

The deferred API deliberately does not serialize SDN text and does not pretend
that a backend handle is a registered packed payload. REQ-GPU-SCHED-PAYLOAD-001
remains a follow-up: use the existing bounded DrawIR v3 generation store only
after replacing its text-growing hash in the hot path.

## Acceptance evidence

The executable system spec covers “Reserve an epoch and its completion credit”,
“Submit the registered draw payload”, “Observe pending work without waiting”,
“Publish the provider completion”, and “Retire resources after native ownership
ends”. It checks delayed completion, duplicate/stale transitions, cancellation,
completion-credit exhaustion, resize generations, malformed payloads, strict
CPU-callback rejection, and disabled-dispatch negative controls. Queue routing
is not device-execution evidence; native timestamps/fences/presentation and
CPU-residency telemetry remain live-hardware gates.

The initial focused unit suite (4 scenarios) and system contract (3 scenarios)
passed on the available `macos-arm64` test runtime on 2026-09-05. This validates
the stated queue model, not physical Vulkan work.

## Parallel lanes

| Lane | Owner | Deliverable |
|---|---|---|
| Queue hardening | Sol | Deferred APIs and focused unit specs |
| Architecture review | Astra | Contract/layering review |
| Merge and acceptance | Codex | Plans, system spec, final review |
