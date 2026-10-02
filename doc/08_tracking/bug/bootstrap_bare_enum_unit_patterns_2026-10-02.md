# Bare enum unit patterns become duplicate MIR defaults

Source review links the Windows Phase 4 lifecycle closure's B5b duplicate-default
diagnostic to `MemoryOrdering` alternatives in `std.nogc_sync_mut.atomic`.
The imported module is present. Flat AST conversion deliberately represents bare
identifiers as bindings; HIR previously accepted every binding as irrefutable.
Exact native diagnostic provenance remains to be confirmed with the reproducer.

The repair indexes nullary variants by consumer-local enum symbol identity before
function bodies lower. Match lowering uses the scrutinee's expression type or its
declared symbol type to distinguish an owned variant from an actual binding.
Imported aliases receive their own identity. Registry lifetime is one HirLowering
module and is cleared by the existing context reset; no frontend/global root is
introduced. Non-unit variants, unknown names, mutable bindings and unrelated enum
names retain binding semantics. MIR duplicate-default validation is unchanged.

Regression artifacts:
- `test/unit/compiler/hir/bare_enum_unit_pattern_spec.spl`: owner discrimination,
  unit/payload distinction, mutable/catch-all/wildcard cases, consumer alias.
- `test/fixtures/compiler/bare_enum_unit_pattern_native.spl`: executable exit-zero
  contract selecting both variants, qualified alternatives and a real catch-all.
- `test/fixtures/compiler/bare_enum_duplicate_defaults_invalid.spl`: compilation
  must still reject two genuine default arms.

Validation status: source review only; executable tests and native bootstrap
verification are pending. The available self-hosted Windows compiler e7ec89c1
predates this patch, and the bootstrap manager owns the host's bounded memory
slot. Do not report a native PASS until a compiler containing the patch builds and
runs the fixture and required compiler/MCP checks.

Separate failure group: unresolved AtomicI64 `load` / `compare_exchange` remains
unfixed. Its local/global discriminator must run after memory admission. Existing
global Struct provenance registration already exists and must not be duplicated.
