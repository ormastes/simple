# Same-name methods on one owner collapse onto one `Owner::method` symbol (Phase-3 run-16)

- **Status:** workaround landed (source); compiler fix committed, unexecuted
- **Found:** Phase-3 run-16, `build/phase3-ref/run-16/build.log`, producer p2shard-9
  (capsule `07c652daea41…`), source head `7d86e04a5ab`, backend cranelift aarch64.

## Symptom

Two codegen failures, one mechanism: `method_symbol_name`
(`src/compiler/20.hir/hir_symbol_table_methods.spl:403`) mangles a method as
`Owner::name`, with no trait or arity part, so two bodies with one name on one
owner share a symbol.

1. `plugins.backend_cuda.cuda_type_mapper`:
   `cranelift: AOT define_function error: Duplicate definition of identifier: plugins.backend_cuda.cuda_type_mapper.CudaTypeMapper.map_array`
   The trait impl does not write `map_array`. A later `impl CudaTypeMapper:`
   block does. Trait-default injection (`trait_impl_lowering.spl` `lower_impl`,
   `if not methods.contains_key(default_fn.name)`) checks only the trait impl's
   own methods, so it also defines the default body under `CudaTypeMapper::map_array`.
   All 8 `TypeMapper` implementors have this shape: llvm, cranelift and
   interpreter (compiler), plus c, cuda, vhdl, vulkan and wasm (plugins).
   That is 47 methods: `map_type`/`map_struct`/`map_array`/`map_tuple`/`map_union`/
   `map_function`/`size_of`/`align_of`.
2. `plugins.backend_lean.lean_backend`:
   `inst573 (v453 = call fn40(v440, …, v452)): mismatched argument count … got 7, expected 3`.
   `LeanBackend` defines an inherent `export_function` (self + 6 params, :796) and
   `impl VerificationCodegen for LeanBackend` defines `export_function` (self + 2).
   The 7-arg calls at :722/:754 bind to the 3-param signature.

## Repro (native-build, cranelift, aarch64, p2shard-9 producer)

One-file fixtures. Red results:
- trait default `map_array` plus an inherent `impl Cm: fn map_array` gives
  `Duplicate definition of identifier: app.zz_r16_probe.b.main.Cm.map_array`.
- inherent 6-param `export_function` plus a trait-impl 2-param `export_function`,
  called with 6 args, gives `got 7, expected 3`.

Green results (same producer):
- override moved into the trait impl: builds, prints `i1[4]struct2x`.
- inherent renamed to `export_mir_function`: builds, prints `x15`.

## Fix

- Compiler: simple-boot-p2shard commit `18c3036a247` (branch
  `work/r16-trait-default-inherent-override`). `record_impl_textual_method_keys`
  indexes the methods written in every impl block before lowering. Injection binds the
  written symbol instead of defining a second body. Spec
  `test/01_unit/compiler/traits/inherent_override_of_trait_default_spec.spl`.
  Not executed: no rebuilt compiler yet.
- Open compiler gap: a trait-impl method and an inherent method with the same name on one owner
  (case 2) get no diagnostic. They silently share a symbol.

## Workaround (source, this commit)

- `# @workaround bug=trait_default_inherent_override_duplicate_symbol_2026-10-24`:
  the 47 overriding methods move from the inherent impl into the
  `impl TypeMapper for X` block, unchanged. Their signatures are identical to the
  trait's, and the multiset of non-blank lines is identical per file.
- lean: the inherent `export_function` is renamed `export_mir_function`.
  It has no external callers.
