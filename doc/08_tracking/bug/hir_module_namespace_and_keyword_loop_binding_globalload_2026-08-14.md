# HIR module namespace and keyword loop binding become `GlobalLoad`

Status: FIXED IN SOURCE / TARGET RUNTIME UNAVAILABLE —
`/root/compiler_globalload_fix` (2026-08-14)

## Evidence

The retained current-source bootstrap probe
`build/native_probe/arm64-server-prereqs/current-cli-cycle2.time` reports 31
Cranelift body failures. Thirty are the same category: module-only relative
imports such as `mod file_system.file_ops` leave the local namespace name
unbound, so qualified expressions reach MIR as `GlobalLoad("file_ops")` (also
`types`, `dir_ops`, and `path_ops`). The remaining failure is
`Column.value_counts`, where the declaration keyword `val` is used as a loop
binding and later reaches MIR as `GlobalLoad("val")`.

## Root cause

HIR import registration tests namespace absence through
`symbols.lookup(module_alias) == nil`. The staged native ABI has known
`Option<SymbolId>` presence/match hazards; this guard can report an absent
namespace as present and skip `SymbolKind.Module` definition. The symbol table
already provides the aggregate-free `lookup_or_invalid` API for this boundary.

Separately, permitting `val` as an ordinary loop binding is ambiguous with the
declaration keyword and is not a stable native-build source form. The affected
table owner should use a non-keyword binding.

## Acceptance

- Module-only imports use `lookup_or_invalid` to decide whether to define their
  namespace.
- A focused HIR regression proves a relative dotted module namespace is bound,
  its qualified callable lowers to `HirExprKind.NamedVar`, and that callable's
  `defining_module` is the imported owner.
- No `Column` method uses the declaration keyword `val` as a `for` binding;
  `value_counts` and adjacent operations use the non-keyword name `item`.
- Verification remains targeted/static; the capped full compiler build is not
  rerun and `build/bootstrap/native_cache` is preserved.

## Verification (2026-08-14)

- Static acceptance gate: PASS. The Option-sensitive guard is absent, the
  `lookup_or_invalid` guard is present, every `Column` loop over `self.data`
  uses the non-keyword `item` binding, the focused spec contains the relative
  `mod` reproducer plus callable-`NamedVar` owner assertion, and
  `git diff --check` passes.
- Focused executable spec: unavailable. The retained stage-2 CLI exposes only
  `compile` and `native-build`; `test` returns `unknown command 'test'`.
- Focused `compile --format=smf`: attempted once and failed on pre-existing,
  unrelated compiler/spec-closure errors (`std.spec` helpers and parser helper
  names unresolved, plus the known generic-native limitation). It did not
  report this regression's `file_ops` namespace as a failure.
- Per instruction, the full compiler/native build was not rerun and the shared
  native cache was neither deleted nor written by this lane.
