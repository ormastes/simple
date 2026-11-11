# Stage 2 fails: `= None` defaults are not call-site constants for the seed (release/1.0.0)

- Status: fixed (PR #8414)
- Found: 2026-11-12, Windows Stage 2 trust-root lane (`bootstrap-windows.sh --full-bootstrap --stop-after-stage2`) on `8289600e9cb`
- Component: seed HIR lowering (`src/compiler_rust/compiler/src/hir/lower/expr/calls.rs`), pure-Simple HIR lowering (`src/compiler/20.hir`)

## Observation

`FAILED FILES (15)`, every one `hir: Unsupported feature: call to X omits
argument N whose default is not a call-site constant`: `emit_resolved_direct_call`
(arg 4, `SymbolId? = None`), `lower_module` (arg 4, `[i64]? = None`),
`hir_cache_key` (arg 6, `HirTargetConstraints? = None`),
`mir_hir_project_encoded_module_in_owned_scope_v1` (arg 6), and the
`MirCallOrigin.Source` enum-path defaults of `cl_translate_const_value` and
`{a64,rv32,rv,x64}_lower_const`. Plus `llvm_type_mapper.spl`: `case Nil:` in
`map_primitive` is not a `PrimitiveType` variant (irrefutable binding).

## Root cause

`d5943d12405` (2026-11-09) replaced `= nil` defaults with `= None` in
`src/compiler/50.mir`, as the language rules require (nil only inside
`unsafe`; the empty value is an Option). The seed's `is_constant_default`
admits `Expr::Nil` but not the identifier `None`, although `lower_identifier`
lowers a bare `None` to the same `HirExprKind::Nil`. Every cross-module call
omitting such a default therefore became a lowering error.

## Fix (both lanes, same shape)

- Seed `is_constant_default` admits `None`; `lower_function` rejects a
  `= None` default on a parameter not declared `T?`; `lower_call` rejects a
  literal `None` positional argument at a non-optional parameter in safe
  code (`ctx.unsafe_depth == 0`), using the callee's HIR parameter types
  (one lookup, only when an argument is a literal `None`).
- Pure-Simple `lower_param` rejects a `= None` default on a non-`T?`
  parameter; `record_call_arity_rows` marks non-Option declared parameters
  with `!` and `check_call_arity` rejects a literal `None` bound to such a
  slot when `unsafe_block_depth == 0`.
- `lower_module`'s `MirModule? = nil` default became `= None`; the five
  enum-path defaults are passed explicitly (an enum path is not a constant);
  the `PrimitiveType` `case Nil` arm is dropped.

## Follow-on: Windows link of the now-compiling Stage 2 closure

With every file compiling, the same lane failed one gate later:
`link failed: 20 undefined symbol(s) with SIMPLE_NO_STUB_FALLBACK=1`
(`rt_hook_*` x8, `rt_hlt`, `rt_cli`, `rt_baked_fs_byte`, `rt_byte_char`,
`rt_bytes_concat`, `rt_bytes_slice`, `rt_copy_user_byte`,
`rt_desktop_pci_get_field`, `rt_embedded_host_rsa_{pkcs8,public_blob}`,
`rt_hda_pci_probe_set_mode`, `rt_arm_elf64_direct_entry`), every one
referenced only by its thin wrapper in `src/lib/nogc_sync_mut/sffi/host.spl`
(`mod_1517.o`). None has a definition in any runtime lane (all 20 sit in
`scripts/check/runtime_link_completeness_allow.sdn` as dead externs) and
nothing imports the wrappers. ELF resolves undefined symbols after
`--gc-sections`, so the dead wrappers vanish there; COFF (ld.lld `-m i386pep`
and lld-link) resolves before `/OPT:REF` and rejects them, and the seed's
gc-parity stub retry is disabled under strict mode. Fix: delete the 20 dead
wrappers (deletion over stubs), prune their allow-list rows, and mark their
`rt_alias_map.sdn` rows `class: missing`.

## Specs

- Reproducing: `src/compiler_rust/compiler/src/hir/lower/tests/expression_tests.rs`
  `none_default_is_constant_and_none_never_reaches_non_optional_param` (seed).
- Generalization: `test/01_unit/compiler/20.hir/bootstrap_regressions/call_site_arity_spec.spl`
  describe "None never reaches a non-optional parameter in safe code"
  (positional, named, `T?` accepted, `unsafe` accepted, `= None` default).
