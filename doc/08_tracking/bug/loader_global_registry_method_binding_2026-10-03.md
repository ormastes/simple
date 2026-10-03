# Loader global dictionary receiver provenance

Status: current pure Phase 2 native failure observed. A declaration-metadata
omission is established in source and repaired in the isolated candidate.
Behavioral/compiler regressions and native verification remain UNRUN.

## Exact failing lineage

- Source: `43f626850b6a5531e89110f75cd1eaedc24adcd1`.
- Pure Phase 2 producer SHA-256:
  `e58968bba401407bb04d6b581e62cf1dcf480847ec56338bb7a06ad4003283ff`.
- Entry: `src/compiler/99.loader/compiler_ffi.spl`.
- Evidence: `D:/dev/ubuntu-release-43f626-recovery-20261003/direct-admission-attempt2/failure-categories.json`
  and its `init-allowed/stdout.log` / `stderr.log`.
- Compile exit 1 after eleven modules reach MIR. Admission succeeded; semantic
  compilation did not. The category file's sixth `contains` row is the terminal
  summary repeating the first error, not a sixth distinct callsite.

## Discriminating source evidence

The real implementation is
`src/compiler/99.loader/loader/compiler_sffi.spl`; the two outer modules are
compatibility re-export facades. The five distinct `contains` errors, one
`remove` error and five context-method errors match the module-global
`CONTEXT_REGISTRY: Dict<i64, CompilerContextImpl>` consumers: five guards,
registry removal, two `instantiate_template` calls, `infer_types`, `check_types`
and `get_stats`. Four `self.type_cache` / `self.instantiation_cache` contains
sites are not reported. Even `get_stats` uses an explicitly typed local.
This points first to global dictionary receiver/value provenance, rather than
text `contains` or missing source methods. Aliased diagnostic line 34 alone
does not prove individual callsite identity.

The MIR implementation already tries to preserve global semantic types:
`try_lower_global_read` in `_MirLoweringExpr/expr_dispatch.spl` reads the
symbol-table declaration, records HIR metadata and marks Dict/array handles.
`lower_const` registers global IDs and initializers, while runtime initializer
lowering derives actual storage from the initializer. A Dict handle's scalar
storage must not replace its semantic key/value types. Instrument/inspect this
handoff before modifying method registration. The eleven separate `infer-arm`
errors and two iterable errors remain independently unresolved.

## Source repair

`declare_module_symbols` in
`src/compiler/20.hir/hir_lowering/_Items/module_declarations_bootstrap.spl`
registered every module constant with `type_=nil`. Later,
`lower_hir_const_decl` computed its annotated type only for `HirConst.type_`;
it did not update the symbol. Bootstrap MIR reconstructs its symbol table from
these preserved HIR symbols. `try_lower_global_read` then reads the absent
symbol type, while the runtime initializer correctly uses an i64 storage handle.
The global consequently never receives the Dict marker or nominal value type.

The repair publishes explicit annotations during module symbol declaration,
before function bodies are lowered. It does not evaluate initializers, guess
types for unannotated globals, change physical storage, or annotate callers.
Class/struct symbols are already declared earlier in this pass, so the Dict
value preserves its existing nominal owner identity.

Declaration ordering is explicit: `module_build.spl` resolves imports and
package siblings in Pass 0 before invoking `declare_module_symbols`. That
declaration pass registers every class, struct, enum, trait and type-alias
template before reaching constants. Source declaration order therefore does
not require a class to appear before a global using it. The unit source puts
the globals and alias before the class and asserts that an unannotated
constant's symbol remains untyped, preserving existing inference behavior.

`test/01_unit/compiler/mir/global_registry_declared_type_spec.spl` checks the
actual symbol metadata for both `var` and `val`, then lowers dictionary methods
and inferred/declared class-value calls through the real frontend/HIR/MIR path.
The original eleven-module loader still needs changed-producer verification;
the source finding alone does not establish that every reported error is fixed.

Source review accepted this ordering and the focused change. No native test
runner was available at preparation time; the Linux verification queue retains
the native oracle behind the currently running Phase 3/4 work. The fix must not
be merged on static verification alone.

## Reduced native gate

`test/fixtures/bootstrap_builder/global_registry_method_binding_main.spl`
retains a typed module-global dictionary of class values, contains/remove,
inferred and explicitly typed index results, instance method calls and mutable
writeback. Equivalent local and class-field dictionaries are controls.
The source is standalone and needs no loader/JSON closure.

Build with the pinned producer, exact runtime/provider receipt,
`SIMPLE_NO_STUB_FALLBACK=1`, and a private phase/producer/closure cache after
root admits its resource reservation. Require compile success, exit zero and
`GLOBAL_REGISTRY_METHOD_BINDING_NATIVE_PASS`. If the reduced fixture passes,
add the two-hop export facade to discriminate closure/symbol remapping; do not
pretend that its pass fixes the eleven-module loader entry. Preserve the frozen
43f source and compare any isolated candidate against the original failing
entry. No additional build has been launched for this investigation.

The additional `test/fixtures/bootstrap_builder/global_registry_alias/` graph
exports a class and type alias from `provider.spl` and imports both using `use`.
Compile `main.spl` with that fixture directory as an explicit source root.
Require exit zero and `GLOBAL_REGISTRY_IMPORTED_ALIAS_NATIVE_PASS`; failures
21–25 distinguish initial state, insertion, inferred value, declared value and
removal. Its expected class method result is 73. This graph avoids the separate
from-import scanner defect and is also UNRUN.
