# `class CompilerCompilationContext(CompilationContext):` registers no trait implementation

- Canonical id: compiler_compilation_context_class_header_trait_no_impl_2026_10_20
- Date: 2026-10-20
- Status: open (latent; no failing build yet)
- Location: `src/compiler/80.driver/pipeline/compiler_context.spl:16`
- Defect: same as the `LinkerCompilationContext` failure fixed in PR #3914. The class-header
  spelling `class X(Trait):` produces no `impl Trait for X` (MIR native trait registration reads
  only `module.impls` with `has_trait_`), so converting a `CompilerCompilationContext` into a
  `CompilationContext` trait object fails with "missing native trait implementation:
  compiler.common.compilation_context::CompilationContext for ...CompilerCompilationContext".
  Its methods have also drifted from the trait (`compile_template -> text` instead of
  `Result<TemplateCompiledUnit, text>`, `di_container() -> has_DiContainer` instead of
  `DiContainer?`, `record_instantiation(InstantiationEntry)` instead of `InstantiationRecord`,
  no `instantiation_count`).
- Why latent: no current source constructs it as a `CompilationContext` (no call site of
  `CompilerCompilationContext(` outside its own file), so phase 3 does not hit it.
- Fix: same shape as `src/compiler/70.backend/linker/linker_context.spl` in #3914 — plain class
  holding the data plus `impl CompilationContext for CompilerCompilationContext` with
  signatures matching `src/compiler/00.common/compilation_context.spl:185-205`. Or delete the
  class if it stays unused.
- Related: the class-header form itself should either be rejected by the parser/HIR or lowered
  to a real impl; today it is silently accepted.
