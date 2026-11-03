# Annotated modules refuse flat-AST/HIR body cache (perf)

Status: open, P1 (blocks E-MC-REP-001 annotation rollout; owner decision 2026-11-03).

## Root cause
No typed codec for `RepresentationDeclarationV1` (src/compiler/00.common/assurance/representation_manifest_v1.spl:14):
- HIR: `hc_enc_opaque_representation_declaration_v1` / `hc_dec_...` reject with E-MC-REP-004
  (src/compiler/20.hir/hir_codec_support.spl:619-625; generated mirror hir_codec.spl:110,622).
- Flat AST: src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:1315,1365 calls
  `representation_parser_refuse_restored_metadata_v1` (core/representation_declarations_v1.spl:57).
Any module with source `@representation_boundary` therefore re-parses and re-lowers every build.
Annotating the 196 E-MC-REP-001 modules would make that the common case.

## Fix
Encode the struct field-wise (text, i64, Span, [Span], [text], bool, optional manifest
with schema_version/kind/reason/reviewers/capabilities). Bump the codec version. Keep
`source_digest` in the record and fail closed (cache miss) when it does not match the current
source digest. Regenerate hir_codec.spl from the generator; do not hand-edit it.

## Spec (write first)
An annotated module is lowered twice. The second load must hit the body cache with the metadata
unchanged. Changed metadata must miss. Explicit budget: the warm load costs no more than 1.5x
the warm load of an unannotated twin.

## Guard
A regression spec asserting no codec path emits E-MC-REP-004 for a well-formed declaration.

## Risk
This changes the 10.frontend/20.hir cache format that stage3 reads. Land it, mark it
verification-pending, and verify it on the next stage3.
