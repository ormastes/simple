# TODO: [gpu][P2] Exercise the Metal provider probe on a host where metal_available() is true

Date: 2026-09-06
Lane: GPU scheduler hardening (plan doc/03_plan/ui/gpu_scheduler_hardening_gpu_resident_rendering.md)
Rule: this may not be closed by a source scan, a routing receipt, or an interpreter run.

Under the current seed the Metal probe reports unavailable (`rt_metal_is_available`
returns false) even on this Apple M4, while the same device answers through the
Vulkan/MoltenVK lane. The probe's available branch is therefore never executed here.

Closing evidence: a probe transcript from a host where `metal_available()` is true, showing a
non-empty device name and driver identity, and the conformance grade it produces.
