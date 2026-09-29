<!-- codex-architecture -->

# Dynamic runtime/kernel provider composition — TLDR

Extend the selected minimal-core, demand-loaded-provider plan. This is a design
integration, not evidence that bootstrap or aspect dynload is complete.

- Preserve K0 loader/admission/value ABI, compiler-private HIR/MIR and weaver;
  preserve the selected K1 LLVM/Cranelift bootstrap composition.
- Package optional Cocoa/GPU/media/tooling/service implementations behind coarse
  stable provider interfaces. `rt_cocoa_*` has one runtime dynload owner.
- P0: bootstrap authority must bind the actual runtime cdylib and dependencies;
  static archive evidence cannot authenticate a separately loaded library.
- Reuse SCI, `SimpleProviderQueryV1`, KPF generations and existing loader owners.
  Admit immutable exact bytes before native constructors execute; full hashes
  identify bytes but do not establish publisher trust.
- Compile-time weaving, provider loading and aspect activation are distinct.
  A dynamic-aspect claim requires the mapped advice payload to execute with
  joined mapping/registry/generation evidence. Facet language choices remain open.
- Hot paths use pinned dense slots; generations own callbacks, continuations,
  resources and fences until quiescence. Never infer physical unmap from close.
- Keep kernel/drivers MDSOC-only; ECS business state is userland-only.

Selected budgets: startup metadata <2 ms above baseline; variant selection p95
1/25 ms warm/cold; batch dispatch overhead ≤2%; inactive catalog ≤2 MiB RSS.
Use each budget only on its original named fixture. No-import hello must load
zero optional providers. Content/policy/generation changes invalidate cached
bindings; static weaving also invalidates affected consumers.

[Architecture](dynamic_runtime_kernel_provider_composition_2026-09-22.md) ·
[Design](../../05_design/compiler/dynamic_runtime_kernel_provider_composition_2026-09-22.md) ·
[Tests](../../03_plan/sys_test/dynamic_runtime_kernel_provider_composition_2026-09-22.md)
