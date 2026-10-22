# Lean declaration architecture

Use one plugin-owned semantic planning leaf shared by the two retained backend entrypoints. Do not add a MIR schema, loader registry or independent backend mirror. `lean_plan_type_declarations(MirModule, namespace)` returns `Result<LeanTypeExportPlan, CompileError>`. The plan contains a typed context and deterministically ordered typed declarations. `lean_context_type_to_lean` resolves admitted nominal references and delegates primitive refusal policy to the canonical mapper.

Both owners' `export_types` validate the complete plan before builder emission and return its context. Both public module APIs propagate errors and supply `Some(context)` to `export_function`. A direct function export without context retains context-free mapping. Actual function body translation remains canonical and independently refuses unsupported aggregate operations.

Generated semantic types live in `__MirTypes`; identity/layout metadata lives in `__MirTypeMetadata`. Nominal references use `_root_.<module namespace>.__MirTypes.<quoted source name>`. Root-qualified primitive references avoid source-name shadowing. Prefix-overlapping type names and function collisions with reserved namespaces fail closed. Existing structure/inductive builder methods emit declarations; no proof term, sorry, axiom or layout equivalence is introduced for declarations.

The historical Minimal verification level still emits function-signature axioms. This packet does not upgrade Minimal to proof evidence, change its contract, or use it in acceptance tests. Contracts-level outputs and declarations are the executable acceptance path here.
