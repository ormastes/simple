# SCV semantic issuer producer investigation — 2026-10-27

STATUS: BLOCKED — complete compiler producer lifecycle remains outstanding.
Execution: NOT_RUN. No admitted general runtime is available to this lane.
This report records inspected source and authored regression assertions, not
red/green execution, branch coverage, production admission or verify PASS.

## Exact current lifecycle

1. `semantic_scope_live_owner_v2.begin_scope_v2` retains a prepared attempt,
   generation, direct read pin and the requested source universe.
   `issuer_attempt_context_v2` exposes an exact copied diagnostic context while
   the attempt is live and Preparing. Context fields cannot prove execution.
2. `semantic_scope_issuers_v2.issue_declaration_scope_v2` checks retained surface
   alignment and equality between surface paths and the supplied source universe.
   The trait, aspect, macro and body issuers inspect their supplied owner values.
   Their conditional negative witnesses come from empty local collections;
   those collections contain no proof that every source was semantically visited.
3. `SemanticScopeIssuerReceiptV2` retains one owner revision and an opaque handle.
   `validate_issued_scope_v2` checks handle, exact attempt and current revision,
   then returns `Unknown`, `universe_complete: false` and
   `gateway_install_available: false` for every dimension. Revision validity is
   useful diagnostic evidence; it is not source-universe completion authority.
4. `install_semantic_issuer_v2` validates that receipt, then
   `_issuer_candidate_v2` rejects its unavailable projection. `seal_scope_v2`
   requires all five retained/current issuer slots, so it cannot issue the live
   completeness grant through the present adapters.
5. `preflight_three_payload_parse_v3` reserves and starts a run, reads bounded
   physical files and completes parse preflight. Its result is a parse result.
   `execute_three_payload_compile_v3` refuses with `AuthorityUnavailable` before
   reserve because no owned parser-state profile and complete semantic pipeline
   are wired to it. No inspected production caller invokes issuer installation
   or compile execution from the compiler driver orchestration.
6. `VerifiedThreePayloadWorkerResultV2` has private fields and projection/
   publication consumers, but there is no constructor invocation in its owning
   module. The V3 compile API also returns a distinct compiled-result type;
   its eventual success cannot silently substitute for the V2 result required
   by `ScvSemanticOwnerContextV1`.
7. `declaration_semantic_issuer_install_boundary_v1` explicitly has no issuance
   transition and returns `AuthorityUnavailable`. The SCV semantic adapter
   therefore cannot accept a completed compiler read manifest/root candidate.

## Actual compiler work that exists

- `driver_source_parse_retained.parse_all_impl` and
  `driver_source_parse_streaming.parse_all_streaming_surfaces_in_place_impl`
  parse real compiler source inventories. The latter retains canonical paths,
  source contents, surface builder state and selected worker closure. These are
  prospective integration points for observed source traversal, not existing
  five-owner completion leases.
- `driver_hir_pipeline_passes.type_check_impl` is explicitly a compatibility
  no-op and cannot supply semantic execution evidence. Its comment locates
  Check-mode inference inside `lower_and_check_impl`.
  `run_typecheck_warn_pass` reaches
  `hir_typecheck_consumer_v1.collect_module_typecheck_receipt_v1`.
  That consumer performs actual HM inference, frontend, visibility and cfg
  checks, but returns diagnostic arrays; it does not return an authenticated
  `SemanticQueryReadManifestV1` or resolver/generated/provider closure.
- `hir_body_semantic_lease_v1.hir_body_archive_semantic_lease_v1` loads an
  archive in an owned scratch scope, invokes real per-body checks and promotes
  their diagnostic result. Its header explicitly calls this an inactive
  adapter and leaves value-layout/collection/mono/MIR admission separate.
  Its digest and checked-function count do not authorize a complete live grant.
- `three_payload_semantic_closure.build_three_payload_semantic_read_manifest`
  builds a canonical manifest from the supplied symbolic inputs. Canonicalizing
  a supplied input set does not prove it contains every semantic read that
  actual compiler execution performed.

## Required implementation order for the real producer

1. Write an integration spec that invokes the actual compiler producer on a
   captured two-module program and observes owned traversal, parsed content,
   semantic checks, installed five-owner capabilities, executed query reads and
   the exact accepted result. Bind the test to an admitted runtime identity.
2. Instrument the actual source/resolver owner to retain immutable completion
   state for canonical paths, namespaces, selected variants, candidates and
   negative lookups, directory membership, generated inputs and providers.
   A missing, newly appearing or unobserved source must prevent completion.
3. Retain actual trait/coherence, aspect/order, macro/CTFE and verified-body
   owners from that same execution. Each owner must authenticate its exact
   request, source closure, revision, generation and dependency enumeration;
   caller-supplied booleans, expected digests or empty objects cannot grant it.
4. Install and seal those capabilities only after all phases finish, then run
   the owned semantic compiler through the bounded broker. Record actual query
   reads, parser profile, execution limits and physical reads. Cancellation,
   stale pins, owner mutation and failure must retire authority.
5. Add a reviewed owner-only bridge for the versioned worker result consumed
   by the SCV adapter, or consistently migrate its consumers. The bridge must
   validate the execution binding and retain result custody.
6. Compare the complete compiler snapshot/manifest with the full SCV captured
   universe, including configuration, target, compiler, runtime, environment,
   namespace/path normalization and provider locks. Exact UTF8 paths alone do
   not prove compiler NFC normalization for non-ASCII paths.
7. Archive the actual validation receipt, then let the parent publish its
   authenticated accepted root. Exercise malformed parse, semantic errors,
   omitted reads, changed negative candidates, stale revisions, substituted
   providers, cancellation and corrupted receipts as independent negative
   controls before permitting reuse.

This spans source/resolver ownership, four conditional semantic producers,
owned execution and result publication. A narrow constant or DTO change cannot
complete it safely. No production authority gate was changed in this lane.

## Regression work and validation

- Tests-first commit `e3d3951d83b` checks all five diagnostic projections for
  unknown/incomplete/uninstallable state, rather than checking only declarations.
- A new unobserved-source regression parses one actual module, requests an
  additional source, requires declaration refusal and prevents optional empty
  owners from turning their diagnostic absence witnesses into completion.
- Existing misleading test wording about running every real owner phase was
  corrected. The handwritten manual now explains the same boundary.
- Runtime spec execution, SPipe docgen/maintain and compiler/core/MCP checks:
  NOT_RUN. Whitespace and layout audits are static evidence only.

The requested complete SCV BuildRunner semantic reuse feature is not delivered
by these regressions. The production issuer/executor work above remains open.
