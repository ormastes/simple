# simpleos-os_scheduler

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-SOS-017"></a>FR-SOS-017 | Discover hardware scheduler topology domains | Replace the current flat default `SchedulerTopology` with hardware-discovered scheduler domains for SMT siblings, shared-cache/package groups, and NUMA nodes. The flat topology must remain the fallback for tests and early boot. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| <a id="feature-FR-SOS-018"></a>FR-SOS-018 | Add idle-path balancing and full wakeup preemption | Extend the conservative unblock/timer rebalance hooks with idle-pull balancing and fair-class wakeup preemption. Woken interactive/fair tasks should be able to preempt when their eligible virtual deadline is earlier than the current running | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| <a id="feature-FR-SOS-019"></a>FR-SOS-019 | Add RT bandwidth throttling and priority inheritance | Add safety controls before exposing unrestricted realtime policy to user workloads: global/per-CPU RT bandwidth throttling and priority-inheritance mutex support for bounded priority inversion. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| <a id="feature-FR-SOS-020"></a>FR-SOS-020 | Complete deadline CBS and deadline-miss tracing | Extend deadline admission into a full EDF plus CBS runtime model with budget replenishment, per-task deadline-miss counters, and scheduler trace events. - [x] Runtime budget is consumed and replenished by period/deadline rules. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
