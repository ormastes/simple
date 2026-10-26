# SMF serializer has an unresolved redundant AST import

Status: local candidate; executable verification pending.

The test-runner source capture found `use ast.{FunctionDef, StructDef, ClassDef,
EnumDef, TraitDef}` in `src/compiler/80.driver/smf_serialization.spl`. The same
file already imports all five names from `compiler.frontend.ast`. The committed
native-entry resolver provides no established bare `ast` owner for this route;
both frontend AST facade paths exist, so inventing an alias would be ambiguous.

Remove only the redundant bare import. Keep the existing canonical import and
all serialization bodies unchanged. This removes an unresolved named edge;
it is not evidence that the full test-runner closure compiles.

New regression: `test/01_unit/compiler/driver/smf_serialization_import_owner_spec.spl`
loads the real serializer and verifies the complete empty GTPL version-two wire
header. Existing `test/01_unit/compiler/linker/smf_enum_def_round_trip_spec.spl`
also exercises populated serialization and deserialization. Both remain UNRUN
for this candidate; no executable TDD or performance PASS is claimed.

The native test-runner rebuild is the integration acceptance gate. Preserve
separate observations for unresolved wildcard imports; this change does not
silently assign those names an owner. Canonical bug DB reconciliation remains
pending a qualified pure CLI. No remote landing before Phase3 and non-regression
requirements pass.
