# Lean MIR declarations — executable specification manual

REQ-MC-007 / lane 07 C2. Source: `test/03_system/compiler/lean_type_declarations_spec.spl` (19 scenarios) and `lean_type_declarations_owner_spec.spl` (4). This manual describes authored tests; execution and generated Lean elaboration are UNRUN.

## Export registered structures and enums

Construct real MIR definitions for `wire.Packet` with U8/I32 fields and `wire.State` with empty/payload variants. Call Contracts-level full-module and regeneration exports. Assert actual Lean structures, exact BitVec widths, qualified payload references and typed discriminant metadata. The compiler-owner spec independently uses Char and verifies no declaration axiom/sorry appears. An actual nominal identity function asserts qualified parameter/result references and translated return body. Empty definitions, nested Result/Array and distinct qualified names have separate scenarios.

## Compare deterministic declaration order

Insert dependency/user definitions in opposite dictionary orders, with lexical user name before its dependency. Assert the production plan orders the dependency first and actual module output is byte-identical. Full/regeneration namespace bodies must agree.

## Retain source layout identity

Mutate U8 to I8 and a field offset, then assert exact changed metadata and changed output. Assert negative and positive explicit enum tags, source symbols, quoted export metadata and C-export identity. These are retained source facts, not a native-layout theorem.

## Reject incomplete or unsupported MIR

Call actual APIs with missing symbols, wrong nominal kind, wrong table keys, duplicate names/members/tags, malformed or reserved namespaces, overlapping type namespaces, unions, bitfields, negative offsets/array lengths, floating-point and raw-pointer fields. Assert named errors. Verify invalid full-table planning leaves an existing builder untouched. Both compiler-owner module APIs must reject unresolved payloads. The previous self/mutual cycle-refusal scenario now asserts grouped inductive output; the [recursive declaration manual](lean_recursive_declarations_spec.md) covers its expanded contract on both owners.

## Evidence limits

No assertion inspects source files or substitutes a second implementation. All tests need qualified execution. The emitted Lean itself must additionally elaborate under admitted Lean/Mathlib. Recursive fixed arrays, further type families, general aggregate operations, native-layout equivalence and FV2 closure remain open. The recursive source packet does not establish execution or kernel acceptance. Minimal-mode historical function axioms are not acceptance evidence.

## Revision 2: generated constructor collisions

For each of `ctorIdx`, `ctorElimType` and `ctorElim`, build a real enum with the reserved member and `Other` (two distinct variants). Both plugin and compiler-owner tests call full and regeneration exports and assert the named member error. Each also invokes `export_types` on an existing builder and asserts its retained contents are unchanged. A valid struct is present in each module, so later declaration failure must still prevent partial emission. These tests are authored and UNRUN.
