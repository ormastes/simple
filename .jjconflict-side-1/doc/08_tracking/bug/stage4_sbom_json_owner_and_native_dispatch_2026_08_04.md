# Stage 4 SBOM JSON owner and native method dispatch

## Status

Physical JSON owner fixed and crossed by the full closure. The native
fluent-method dispatch defect has a reviewed MIR-owner fix and executable
regression; rebuilt-compiler runtime verification remains pending.

## Phase 4 symptom

Fresh x86 Phase 4 cycle 2 crossed the T32 repairs, then HIR lowering stopped in
`std.nogc_sync_mut.sbom.sbom_generator` on unresolved `JsonBuilder`.

## Repair

The SBOM generator now imports `JsonBuilder` and `JsonArrayBuilder` from their
physical owner, `std.common.json.builder`, instead of the common JSON hub. The
focused native contract compiled and linked 26 modules and its document-model
path exited 30. Phase 4 cycle 3 crossed this module.

## Independent runtime defect

When the focused contract executes `generate_sbom_json`, native execution exits
132 with `field access on nil receiver`. GDB resolves the failing call chain to
`JsonArrayBuilder.build -> serialize_sbom -> generate_sbom_json`: the terminal
`JsonBuilder.build()` after `field_array_raw()` was lowered to the unrelated
same-named `JsonArrayBuilder.build()` method. Document construction alone
passes.

The MIR repair derives result provenance from the resolved method SymbolId's
declared `HirTypeKind.Named` return type, stores its module-qualified composite
layout key, applies consistently to instance/static/trait calls, and prevents a
weaker bare-name fallback from overwriting it. The regression now executes both
builders' same-named terminal methods and `generate_sbom_json`. A rebuilt
compiler could not yet be linked with the narrow bootstrap runtime (optional
Cranelift/GUI symbols are absent), and the admitted Stage3 lacks the LLVM
feature, so no runtime PASS is claimed until the next current-head bootstrap.
