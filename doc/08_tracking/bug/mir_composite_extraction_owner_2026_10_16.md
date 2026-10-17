# Remaining direct MIR provider record extractions

Date: 2026-10-16
Bug: BUG-MIR-COMPOSITE-EXTRACTION-OWNER-20261016
Database registration: pending; no admitted database tool available.
Status: source-only candidate; native and broader verification UNRUN.
Base: 99b871a431a (full identity recorded in external manifest).

Remote99b871a added explicit named-record bindings to protect the stage2 composite transport path, but ten directly field-read collection extractions retain inferred bindings. This report records the remaining source pattern; no new crash, hang, or native success at these sites is established.

The bounded followup adds actual canonical type annotations at exactly ten sites: provider_globals function parameters and provider modules; module_lowering computed layout fields, external layout traces, enum variants, inventory modules, prescan parameters, extern parameters, struct fields and class fields. Array iteration uses a raw iterator and immediate typed local. Indexed reads gain only a local type annotation. No casts, field substitutions, guards, traversal order, defaults, payloads or algorithms change.

HirParam/HirField/HirVariant are owned by compiler.hir.hir_definitions; HirModule by compiler.hir.hir_types. Both files already import these terminal modules. FieldLayout is owned by compiler.types._TypeLayout.layout_core, exposed by the existing explicit compiler.types.type_layout import. MirExternalLayoutTraceV1 is owned by compiler.common.native_layout_trace and is already explicitly imported. No new import or competing record is introduced.

Excluded pending separate evidence: the two declaration repository Optional.unwrap record returns, chained module indexing, direct forwarding into typed function parameters, and matched/forwarded enum values. Scalar text/i64/bool arrays and dictionary keys are not classified as named-record extraction defects.

External evidence: remote-review-followup/composite-extraction-followup-source/{owner-and-extraction-manifest.json,inverse-byte-proof.json,source.patch}. Each of the two entire baseline source files is preserved. Reversing exactly the ten binding edits produces byte-for-byte equality and identical SHA256 with each baseline file. This is change-scope evidence, not a semantic runtime test. No placeholder tests or native qualification attempts are added. Review and an independently admitted meaningful engine qualification remain required.