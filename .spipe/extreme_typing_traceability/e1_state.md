# E1 owned signature projection candidate

2026-11-02, base 401883ab000, work/release-1.0.0-fix-primary.

Bounded acceptance (source candidate; execution pending):
1. The retained production typecheck pass requests signature projection inside
   the actual inference consumer after infer_module, before context disposal.
2. Returned facts contain owned scalar/enum/text/array data only, never HIR,
   SymbolTable, Substitution, parser or module-surface objects.
3. Structural type nodes use compiler kind tags and module-local symbol identity;
   bounded substitution traversal detects unresolved/cyclic variables. Explicit
   unknown reasons cover nominal member expansion, generic guarantees, omitted
   declaration kinds, effective export closure and generated stages.
4. Facts reach bounded per-module CompileContext storage. Optional collection
   defaults off for existing archive body leases, whose diagnostic digest and
   lifetime contracts are unchanged. No serialized/cache/admission consumer
   may claim these facts as complete or authoritative publication permission.
5. Real unit/negative specs cover type tags, substitution, symbol ownership,
   budgets, and production consumer/storage plumbing. No string-source tests
   substitute execution. All tests unrun until an admitted runtime exists.

Owned files: new 00.common/api_signature_facts_v1.spl;
new 30.types/type_infer/api_signature_projection_v1.spl;
80.driver/hir_typecheck_consumer_v1.spl;
80.driver/driver_hir_pipeline_passes.spl; 80.driver/driver_types.spl;
80.driver/driver_orchestration.spl (retained product ownership only);
new test/01_unit/compiler/type_infer/api_signature_projection_v1_spec.spl;
doc/05_design/extreme_typing_traceability.md (append candidate status).

Reviewer: /root/design_review. Maximum three source review/fix cycles.
No commits/merges, Rust changes, fatal enforcement or runtime claims.

Source checkpoint: production collector, bounded projector, retained store and
seven execution specs authored. Cycle 1 review found no P0/P1; corrected early
budget error counts, added nonempty production-pass coverage, and moved all
lifetime-spec assertions outside scratch with mutable record promotion.
Sibling substitution paths copy their bounded active-ID list independently.
Cycle 2 final source review requested. Tests remain unrun. Added concise status
to the traceability guide and feature expert route; no operational skills changed.

Final checkpoint: cycle 2 independent source review completed with zero
unresolved reported P0/P1/P2 findings. Owned tracked diff whitespace check passed.
Source frozen for parent review/commit. No runtime, merge or release qualification.
