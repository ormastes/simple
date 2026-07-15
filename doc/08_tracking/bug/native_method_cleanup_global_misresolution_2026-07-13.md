# Native method cleanup global misresolution

**Status (2026-07-15):** source implemented; strict LLVM/Cranelift dispatch
execution remains pending.

Strict `bootstrap_main` linking showed calls authored as `compiled.cleanup()` in a module
with a conflicting wildcard-imported `backend_types.CompiledModule` resolving to
`interp.execution.tiered_jit.TieredJitManager.cleanup` instead of `codegen.CompiledModule.cleanup`.
The wrong binding retained interpreter-only `rt_jit_cleanup` in a hosted native build.

Evidence: `/tmp/.tmpy70sui/mod_308.o` defines `CompilerBackendImpl` and relocates its
process path to `TieredJitManager_dot_cleanup`, while the receiver is returned by
`CodegenPipeline.compile_module` as `codegen.CompiledModule`.

The immediate collision is removed by the owner-specific method name
`release_codegen_module` across all eight callers. A compiler regression should later
prove explicit receiver type/import resolution wins when unrelated types expose the same
method name.

## Pure-Simple root fix (2026-07-15)

HIR method declarations now retain `<module>.<Owner>::method` identity, the resolution pass uses the
module's populated symbol table, and MIR emits the matching owner-qualified symbol. The
focused regression lowers two unrelated `cleanup` owners and proves the codegen receiver
selects its own method. Bootstrap closure lowering now retains impls/method bodies and
uses the same owner-qualified accumulator names. Explicit/glob imports register the
selected type's impl methods under the defining module, including concrete-owner copies
of trait defaults. `release_codegen_module` remains only as Rust-seed bootstrap
compatibility until a fresh self-hosted stage proves the old seed ambiguity is absent.

The focused owner-dispatch regression is present but was not executed in the
2026-07-15 source-only audit.
