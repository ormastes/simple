# SIMD, GPU and SOSIX variations — TLDR

Status: user-selected design, implementation and qualification incomplete.

The [imported proposal](simd_gpu_sosix_variation_final_2026-10-10.md) is corrected against release by the [shared-interface design](perf/item5_shared_provider_interfaces_2026-10-09.md#2026-10-11-variation-and-sosix-integration). Its migration packages belong to the existing Item 5 plan.

- Reuse environment snapshots, target profiles, exact feature/target registries, catalog, admission, bindings and generations. Adapt existing V1/V2 boundaries explicitly.
- Keep one sparse `variants/` resolver and `config/var.sdn`. Layer-owned ISA/ABI/OS/device implementations stay in place; generic bitness differences do not justify copied libraries.
- Distinguish compile target, process capabilities, worker vector state and device generation. SIMD width is not ISA evidence; GPU SIMT is not CPU scalable SIMD.
- Share algorithms and legality, retaining legitimate target lowering differences. Prepared SIMD calls perform no discovery, probes or SOSIX ring submission.
- Reuse SOSIX/SimpleRing operations, wake, leases and retirement for services/GPU resources. Cancellation does not release live native access; no blind replay after uncertain effects.
- Register missing targets and qualify each source/compile/link/bind/execute/parity/performance stage. Preserve all original size/startup budgets and actual DB/webserver on/off comparisons.
- Move or redirect owners, prove parity and rollback, then retire duplicates. Do not mark a platform supported from a folder, source scan, cross-link or unrelated C test.

Proposal P5 means SIMD planning; Item 5 Phase 5 still means Size and Loading Gates. Full bootstrap, real apps and current ARM/RISC-V execution remain required.
