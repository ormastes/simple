# Seed declared-return check rejects valid gradual-typing forms — 542 app files

**Status:** FIXED (validate_declared_return_type now compares semantically)

**Found:** 2026-09-16 ~13:20 local, full bootstrap chain9 on merged main
(810476a68a4), stage2 native-build: "542 file(s) failed to compile", every
failure `hir: Type mismatch: expected TypeId(N), found TypeId(M)` under the
Rust seed.

## Symptom

Any full bootstrap that rebuilds the Rust seed dies in stage 2: the seed
rejects 542 previously valid `src/app/**` files. Single-file repro with the
seed:

```
[jit-fallback] HIR lowering error: Type mismatch: expected TypeId(610),
found TypeId(614) [in src/app/cli/check_entry.spl]
```

## Cause

da8964fe990 (#1025, merged 2026-09-16 01:38 +0900, "native-struct verify
lane") added `validate_declared_return_type` to the Rust seed, comparing the
declared `-> T` annotation's TypeId against the trailing expression's TypeId
by RAW EQUALITY. TypeIds are module-registry-local (`HirModule` owns a
`TypeRegistry::new()`; `register` always allocates fresh ids), and the seed's
type system has several gradual-typing corners where the same logical type
legitimately carries different TypeIds. Raw equality therefore rejected
valid programs in five distinct shapes, observed live:

1. Cross-module / cross-registration named types (same nominal type,
   different registry ids; 542 files at once).
2. Dynamic `[T]` declaration vs fixed `[T; N]` literal.
3. Trailing `[]` empty literal (inference defaults element to i32).
4. Immutable `shared &T` returned where `T` is declared (value-transparent
   references from shared receivers; the self-hosted compiler and the
   interpreter both accept).
5. Trailing `nil` (the language's bottom literal).

The same squash also left 14 failing `hir::lower` tests; those failures were
symptoms of the same strictness (all 14 pass after this fix).

## Fix

`validate_declared_return_type` delegates to `hir_types_compatible`:
ANY/equal/NIL fast paths; numeric pairs; immutable shared references
interchangeable with their inner type (both directions); then a
registry-resolved structural comparison (named aggregates by NAME -- field
layouts legitimately differ between ANY-field fallback copies and
fully-typed declarations -- composites recursively; empty arrays admit any
array; dynamic array declarations admit any fixed size of a compatible
element). A TypeId that does not resolve in the module's own registry
belongs to another module's registry; module-local ids are meaningless
across registries, so those comparisons are admitted.

Round 2 (chain10, 2026-09-16 ~19:30): with #1042 merged, the app closure
compiled but 13 compiler-source files still failed in the full stage2
closure build (single-file `check` could not reproduce them -- module
resolution context changes TypeId allocation). In-context debug
(SIMPLE_SEED_RETURN_TYPE_DEBUG over the exact chain10 native-build
invocation) exposed three more valid-program shapes: numeric tails in `->
bool` functions (the seed itself coerces those); value bodies under an
explicit `-> unit`; fixed-size array literals against declared tuples.

Second line of defense added: when an incompatible pair involves an
AGGREGATE on either side, the mismatch downgrades to a warning and the
program is admitted. Aggregate typing in the gradual corners (trailing
`match` arm unification, cross-module re-registration, ANY-field fallback
copies) is not authoritative in the seed, so a hard error there cannot be
sound; the hard-error scope is primitive-vs-primitive pairs (e.g. `-> bool`
returning text still rejects).

Sibling guard, same class: `get_field_info`'s nominal-Struct branch now
admits -- via the same receiver-blind global lookup the `Any` branch already
uses, refusing ambiguous fields -- a field access on a struct whose local
registry view does not declare the field when the field resolves globally
unambiguously. The self-hosted reference compiler and the interpreter accept
these accesses (observed live: `CompileOptions.target_opt_ctx` sets,
`SymbolId.name` / `Template.name` reads in debug-identity helpers with
incomplete local struct views). Pure typos (field resolvable nowhere) still
fail closed.

Mismatch diagnostics are env-gated behind SIMPLE_SEED_RETURN_TYPE_DEBUG
(registry-resolved HirTypes plus the function name); the aggregate warning
always prints.

Verified: all 310 hir::lower tests pass (14 previously failing from the
same squash, 0 newly failing) plus the new gradual-forms pins; the full
stage2 entry-closure native-build (the exact chain10 invocation, reproduced
in isolation) completes with zero FAILED FILES.

Round 3 (same evening): with the package-resolution fix below, the closure
grew to include the `compiler.mir_opt` package, exposing two builtin-method
gaps in the seed's AOT lowering: `Result.ok()`/`Result.err()` (the MIR
special-lowering table carried unwrap/unwrap_err/is_ok/is_some but not the
std ok/err extraction helpers -- added, mirroring the unwrap_err arm) and
`Array.enumerate()` (a bundled-std iterator method with no AOT builtin --
the single in-closure call site in
src/compiler/60.mir_opt/optimizer_plugin.spl was rewritten as a
semantically identical index loop).

Sibling root cause found while chasing the closure growth:
`module_resolver`'s last-segment numbered-dir fallback resolved
`compiler.mir_opt` INTO the subpackage `60.mir_opt/mir_opt/` whenever a
same-named child package existed, so every name the outer package
re-exported (optimizationconfig_debug and friends) silently resolved to
nothing in entry-closure builds. `resolve_module_in_dir` now prefers the
numbered directory's own package marker (after its same-named file marker)
when the directory's stripped name matches the segment.

## Consequence

CI did not catch the regression because no CI job runs the full bootstrap
closure with a rebuilt seed. A dedicated multi-module import
re-registration unit fixture remains desirable; the full bootstrap closure
is the exercising case for now.
