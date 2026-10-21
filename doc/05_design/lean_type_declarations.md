# Lean declaration detail design

Frozen API: `LeanTypeContext`, `LeanTypeDeclaration`, `LeanTypeExportPlan`; `lean_plan_type_declarations(module, namespace)`; `lean_context_type_to_lean(type, context)`. Both backend owners return `Result<LeanTypeContext, CompileError>` from `export_types`, and accept an optional final context argument on `export_function`.

1. Validate module namespace and reserved declaration namespaces. Collect sorted type-table keys. Check key/definition identity, nonnegative symbols, unique valid source names, and namespace-prefix collisions.
2. Build the module-local symbol-to-qualified-name and symbol-to-kind context. Map complete field/payload types, reject unresolved or mismatched references, collect nominal dependencies, and retain canonical MIR type strings in typed metadata.
3. Reject negative offsets/array lengths, bitfields, unions, duplicate members/tags, generated member collisions, unsupported control characters in export names, and every type refused by the existing exact primitive mapper.
4. Select name-sorted ready declarations until complete. If none is ready, return an explicit unsupported-recursion error. Only after all declarations pass does the backend emit.
5. Emit structures or inductives with ordered members, then typed source metadata. Enum tags remain explicit Int metadata; constructor ordinal is not asserted to equal a native tag. Metadata is evidence retention, not a proof certificate.

ASCII source-name admission intentionally rejects Unicode names and `_root_` components pending a broader checked quoting policy. Type names use quoted segments; field/variant generated-name collisions are refused. Source metadata escapes quotation, backslash, newline, carriage return and tab. Unsupported controls fail closed.

Tests are real calls to public module APIs and the shared planner. A nominal identity function exercises actual function lowering. No parallel interpreter, model-only assertion or source-pattern check substitutes for execution. The packet is authored/unrun until root verifies it.
