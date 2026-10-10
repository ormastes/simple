# Declared enum payload owner lost before nested matching

SOURCE_REPAIR_DRAFT_UNEXECUTED. Actual a0/aa404 Phase3 baseline rejected18 HIR files with86 OR binding records while1142 modules were HIR-accepted and no objects attempted. Tagged source qualifications do not establish permanent repair.

Actual declaration: src/compiler/50.mir/mir_instruction_kinds.spl56, MirInstKind.BinOp(dest:LocalId,op:MirBinOp,left:MirOperand,right:MirOperand). Actual CUDA pattern binds op then matches Add/Sub/etc; actual Vulkan pattern matches nested Eq/Ne/Lt/Le/Gt/Ge directly. expression_components lower_pattern Enum tuple recurses without the declared slot type; Binding defines a niltype symbol. The later match op finds neither attached type nor symbol.type. Nested OR likewise bypasses lower_match_pattern subject-owner threading. This is a concrete source first loss, distinct from canonical unit registration.

Repair authority: prescan declaration-only slot names/types after imports and declaration registration but before function bodies. Imported slot types use the existing imported_surface_type provider projection. Original field-symbol, field-default, variant-symbol and discriminant phases retain their order. Nongeneric enums only; no template substitution guessed. Exact actual enum symbol IDs key metadata; canonical aliases require identical enum declaration name and nonempty defining-module identity. The new table is appended with default and explicitly initialized; the one explicit HirLowering constructor was audited.

Contexts recursively reach declared tuple/struct payload children, nested OR and tuple patterns. Actual variable bindings retain known slot type and original mutable/visibility/span scope. Unit recognition remains expected-owner-only. Qualified enum-owner mismatch is rejected only for a proven enum slot; existing struct-pattern lowering remains separate. Strict OR name equality is not weakened.

Authored real native regression imports actual compiler declarations and actual CUDA/Vulkan pattern forms: all six comparison alternatives must print1 in both forms, arithmetic Add must print0. Named x/y payload mismatch must reject without an object; qualified MirTypeKind.Unit against MirInstKind must reject with owner diagnostic. Unrelated failures are BLOCKED, never negative PASS. All fixtures UNEXECUTED. No producer build or runtime qualification has occurred.

Known limits: generic enum payload substitution is unchanged; late dynamic import pattern registration is unchanged. Prescan currently repeats nongeneric declared-type projection later in full enum lowering; measure if this adds material startup/build cost, then reuse exact-owner slot metadata without forcing caches. No performance claim is made.

Unresolved representation boundary: HirDeclaredPatternEnumSlots stores tuple types, struct names/types and is_struct, without the original VariantKind discriminator. VariantKind.Unit and VariantKind.Tuple([]) therefore share the same empty tuple layout. The existing flat bridge likewise represents payload-less variants as Tuple([]), but this does not prove whether Unit() and a unit pattern without parentheses must be distinguished by every frontend. Extra nonempty unit payload is explicitly rejected; the zero-length unit/tuple distinction remains UNQUALIFIED and needs an actual parser/frontend contract regression before any completeness claim.

## Linux ARM and RISC-V continuation, 2026-10-10

Release `7b45c1e4959bc05af01eb8b212416947195bc4ce` rebuilt 1217 Stage 2
modules and passed both frontend admission modes on Linux AArch64. Its
in-process Stage 2 test-runner prerequisite failed HIR in four modules:
`test_runner_types`, `test_runner_files`, `test_runner_config`, and
`test_runner_main`. Each uses positional `Composite(spec)` patterns against
the named `Composite(spec: text)` declaration. The flat bridge deliberately
retains those names as `VariantKind.Struct`; the new declared-slot check
incorrectly treated positional matching of that declaration as a shape error.

The repair takes positional slot types from `field_types` for a named variant,
in declaration order. Tuple declarations retain `tuple_types`. Pattern payload
shape remains positional, and declared owner, arity, named-field validation,
and concrete-type admission remain enforced. No target-specific behavior is
introduced: ARM and RISC-V share this HIR owner.

`test/fixtures/compiler/named_variant_positional_pattern.spl` exercises distinct
text and integer slots, payload values and a unit alternative. The admitted
old compiler rejects it with the same shape error for both AArch64 and RISC-V.
The rebuilt diagnostic compiler clears HIR on both target paths; its first
unbound build then traps at `spl_cranelift_new_aot_module_config_v2`, so that
attempt is not object-generation or runtime PASS evidence. Rebuilding with the
canonical bootstrap policy and `SIMPLE_BINARY` runtime authority reused 1215
objects and rebuilt two. That runtime-bound compiler produced an AArch64
relocatable object and a native executable: exact stdout `named-positional-ok`,
exit zero, empty stderr. Its explicit source/entry RISC-V build produced an
ELF64 relocatable object with `EM_RISCV`. Wrong positional arity still fails
with the arity diagnostic and no object. RISC-V runtime execution was not
performed: no GNU cross compiler/sysroot was available. The new unit spec
checks exact bound types and wrong arity; it is authored and has not been
executed by a qualified test runner.

Separate open target-routing finding: the positional `native-build file.spl`
path ignores a RISC-V target request and produces `EM_AARCH64` on this host,
even with `SIMPLE_NATIVE_BUILD_TARGET` set. The explicit
`--source ... --entry-closure --entry ... --target riscv64-unknown-linux-gnu`
coordinator path produces `EM_RISCV`. These are distinct observations;
positional-path output must not be accepted as cross-target evidence. This
HIR repair does not fix or qualify that routing defect.

Evidence lives in the isolated Linux worktrees under
`build/native_probe/linux-arm-riscv-phase3-20261010/` and
`build/native_probe/named-variant-pattern/`. Neither Phase 3 nor Phase 4 is
admitted by these diagnostic observations.
