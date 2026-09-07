# TODO: [gpu][P2] Promote a provider from routing_only to full once fences and phases exist

Date: 2026-09-06
Lane: GPU scheduler hardening (plan doc/03_plan/ui/gpu_scheduler_hardening_gpu_resident_rendering.md)
Rule: this may not be closed by a source scan, a routing receipt, or an interpreter run.

No provider grades `full` today, so every receipt in the tree is `routing_evidence_only`
and autonomous submission stays refused. The per-provider seams are marked in
`src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl`. A provider also cannot grade
full without device timestamps, since it could never supply qualifying evidence.

Closing evidence: a provider reporting `fence_token_available=true`, `distinct_phases=true`
and `device_timestamps_available=true` backed by real externs, a conformance report graded
`full`, and an epoch whose `device_execution_proven` flips true on qualifying evidence.
