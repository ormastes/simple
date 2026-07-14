# Native method cleanup global misresolution

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
