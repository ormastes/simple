# GPU Scheduler Hardening — TLDR

Extend the existing bounded Engine2D host-GPU queue; do not create another
scheduler or DrawIR representation. Producers submit immutable/paked payload
descriptors, the provider owns deferred completion and retirement, and legacy
immediate SDN dispatch remains compatibility-only. Strict GPU-scene profiles
forbid semantic CPU fallback but still expose bounded host input/submission/
presentation service work. Next: DrawIR queue and host-GPU queue modules.
