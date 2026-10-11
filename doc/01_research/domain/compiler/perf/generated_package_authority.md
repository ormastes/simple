# Generated package authority and observable acceptance

Research date: 2026-10-10. Scope: existing PSI-REQ-002 and PSI-REQ-005;
this refines implementation of selected requirements, not new requirement options.

## External evidence

Bazel separates declaration from execution: rules declare input/output sets
during analysis, then register actions that produce those outputs. A declared
file alone is not evidence that the corresponding action ran. Inputs must be
explicit and outputs must be produced by an action. These properties support
cache reuse without allowing execution results to invent their own authority.
Sources: [Bazel rules and actions](https://bazel.build/versions/7.6.0/extending/rules)
and [declare_file contract](https://bazel.build/versions/7.6.0/rules/lib/builtins/actions.html).

## Local evidence and implications

`generated_source_receipt.spl` checks declared paths and content digests against
an independently supplied frozen inventory. Its API explicitly requires the
caller to authorize the declaration against a selected build plan. Neither a
matching receipt nor reconstructing that receipt from current inventory proves
that a generator executed. `package_index_acceptance_generated.spl` constructs
input/output fixtures directly and therefore proves receipt admission only.

`cold_hir_compiled_package_outputs_v1.spl` receives optional declaration and
receipt from the artifact itself. Until the driver independently selects an
action declaration, this is self-consistency evidence, not authorization.
`runtime_std_hir_sections_v1.spl` also rejects domain blocks rather than emitting
a fictitious empty generated facet. That refusal must remain until a real
producer supplies output bytes and execution evidence.

There is a second independent gap: `cold_hir_package_drafts_v1.spl` carries the
generated-source digest into a TLDR header, but `package_module_index_builder.spl`
projects no generated-source field into `PackageModuleIndexEntryV1`.
`package_index_route.spl` compares source, export, SMF, ABI, manifest,
initializer and provider witnesses, not a generated witness. Merely adding a
trusted declaration would therefore still not implement generated invalidation.
Treat this as an implementation gap, not an inferred runtime test result.

## Required implementation sequence

1. Select and digest-bind a generator action declaration before execution from
   the frozen build configuration; reject duplicate ownership and ambiguous
   output paths. The compiled artifact cannot author this authority.
2. Execute the declared producer through the owned process/filesystem boundary,
   measuring actual inputs, outputs, exit status and executable identity. Reject
   undeclared reads/writes and missing outputs before snapshot publication.
3. Freeze resulting bytes and bind the execution receipt to their admitted
   inventory. Supply that independently selected authority to the cold bridge.
4. Preserve `generated_source_digest` through index encode/decode and builder
   projection. Use an explicit compatible schema migration; old generations
   lacking that witness must take conservative migration, never implied reuse.
5. Compare the generated witness in semantic transition planning and prove the
   exact owning-package/reverse-consumer invalidation set with unchanged archive
   reuse. Keep unrelated source changes out of generated semantic identity.
6. Execute the existing generated scenarios through the production compiler and
   validate compiler-bound receipts and filesystem observations. Owner-only
   fixture observations remain diagnostic evidence, even when they return zero.

Each step needs executable positive and refusal cases. Current bootstrap
limitations prevent claiming red/green execution, coverage, performance or full
acceptance; preserve that distinction in plan status and manuals.
