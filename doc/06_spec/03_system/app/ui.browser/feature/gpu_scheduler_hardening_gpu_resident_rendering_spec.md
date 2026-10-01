# GPU Scheduler Hardening Acceptance Manual

## Scope

This manual mirrors the executable bounded-queue contract at
`test/03_system/app/ui.browser/feature/gpu_scheduler_hardening_gpu_resident_rendering_spec.spl`.
It proves deferred queue routing and terminal-once behavior, not GPU execution.

## Primary flow

1. Reserve an epoch and its completion credit.
2. Submit the bounded draw routing metadata.
3. Observe pending work without waiting.
4. Publish the provider completion.
5. Retire resources after native ownership ends.

## Evidence limitations

The present provider completion is process-global compatibility routing without
a provider fence/token. A successful receipt cannot establish physical Vulkan,
device timestamps, scene residency, or presentation. Those require the later
live-hardware qualification plan.

The first increment also does not yet register a packed DrawIR payload; it
removes text serialization from the deferred route while preserving the legacy
text dispatch for compatibility.
