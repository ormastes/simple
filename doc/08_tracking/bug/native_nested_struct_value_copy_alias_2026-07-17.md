# Native nested struct copies retain aliases

- Date: 2026-07-17
- Status: source fixed; execution pending
- Severity: P1 silent wrong result

## Symptom

Copying an outer value-type struct rebuilt only its first level. Any nested
value-type struct field kept the original pointer, so mutating
`copy.inner.field` also changed `original.inner.field`. The same shallow loop
was duplicated for plain struct parameters. Embedded `class` fields correctly
remained shared and must continue to do so.

## Root cause and fix

`maybe_copy_struct_value` and the plain-parameter binder emitted one
`GetField`/`Aggregate` layer. The MIR metadata already records each field's
declared nested type and which named aggregates are classes.

Both boundaries now use one recursive value-struct copier. It follows
`struct_field_type_name`, skips `class_type_names`, preserves nil nested
fields with a guarded merge, and rebuilds each non-nil nested value struct.
Normal scalar fields and class references remain unchanged. Cyclic value-type
back-edges remain shared; the type checker should reject such layouts before
that ceiling is removed.

## Regression

The strict dual-backend `nested_struct_value_copy` parity case covers local
binding and plain-parameter copies in one program. It requires nested structs
to remain isolated while the same outer struct's embedded class remains
shared. Linux runs the full parity board; macOS and Windows select the case in
their hosted matrix, and FreeBSD selects it under both LLVM and Cranelift.

Execution remains pending under the current no-runtime/no-compiler-command
restriction.

## Triage evidence 2026-08-17 (read-only lane; classified by CURRENT SOURCE content, not SHA ancestry)

ALREADY-FIXED (source). Content: `maybe_copy_struct_value` (src/compiler/50.mir/mir_lowering_stmts.spl:393-427) no longer emits one GetField/Aggregate layer — it resolves the struct SymbolId and delegates to `copy_struct_value_recursive(init_local, struct_type_name, type_symbol, [struct_type_name])`, and still returns nil (no copy) for `class_type_names`, preserving class-field sharing as required. Not executed natively by this lane (native-build lanes are claimed); the doc's own 'execution pending' caveat stands.
