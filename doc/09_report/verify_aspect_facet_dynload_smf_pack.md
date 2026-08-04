# Verification Report: Aspect Facets and Demand-Loaded SFM Packs

**Date:** 2026-08-04  
**Workspace:** `/home/ormastes/dev/pub/simple-aspect-facet`; the feature
bookmark is synchronized with GitHub and is rebased onto the current
`main@origin` before push.

## Passed evidence

- **PASS — scope isolation:** implementation is confined to the dedicated jj
  workspace; the unrelated dirty default workspace was not edited or folded in.
- **PASS — owner alignment:** the outer multi-module format is `SFM2` SFM
  metadata with opaque ordinary SMFs; no new SMF section or second module reader
  was introduced.
- **PASS — facade audits:** working and staged direct-env/runtime guards report
  `STATUS: PASS`.
- **PASS — executable-spec shape:** mirrored system SSpecs/manuals and focused
  unit/integration specs exist; the final scoped scan found no `pass_todo` or
  `expect(true).to_equal(true)` placeholders.
- **PASS — layout:** `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.
- **PASS — static trace:** every REQ-AF-001..010 appears in focused executable
  evidence; SFM1 compatibility, exact SHA-256 selection, invalid roots/catalogs,
  policy control, coalescing, and prior-generation preservation are asserted.
- **PASS — documentation freshness:** research, requirements, architecture,
  detail design, test plan, agent plan, SFM architecture/design, dynlib guide,
  system manuals, and CHANGELOG were updated.
- **PASS — authoritative static pipeline wiring (static review):** facet
  declarations now survive the production frontend/desugar/HIR pipeline;
  coherence is fail-closed and stores validated `FacetBindingPlan` values on
  `HirModule` for a downstream MIR/codegen consumer.
- **PASS — bounded trust/cache source slice (static review):** exact pack bytes
  can be verified against an externally supplied Ed25519 trust root; mission
  policy rejects unsigned packs; exact-key index/chunk/negative caches are
  bounded and support provider/generation invalidation.
- **PASS — existing-loader mapping source slice (static review):** verified
  module bytes stage through the existing provider-backed `ModuleLoader`, with
  reverse rollback and publication only after mapping/relocation succeeds.
- **PASS — application activation owner (static review):**
  `AspectApplicationRuntime` retains the validated catalog, external trust
  policy, one shared bounded provider cache, and the canonical activation
  coordinator. Mission startup sealing and ordinary quiesce/drain/unload are
  explicit and fail closed.
- **PASS — generation/cache resource model (static review):** lifecycle leases
  are isolated by exact `activation_key@generation`; tokens carry their owner
  and reject replay/forgery. Decoded chunks use the loader's canonical
  `SmfCacheManager`, remain pinned through publication, and are released and
  invalidated only after drain.
- **PASS — dynamic binding publication (static review):** the loader-owned
  `FacetBindingRegistry` stages loader-validated witness owners, publishes an
  exact generation atomically, supports concrete/open-world lookup with
  ambiguity rejection, and removes visibility before unload. The app's
  `acquire_published_facet` returns the record plus its exact generation lease.
- **PASS — resolver registry slice (static review):** resolver-owned aspect SDN
  manifests and descriptors are parsed relative to their declaring manifest,
  canonicalized, escape/collision checked, fingerprinted, and installed on an
  existing `ModuleResolver` without a second resolver.
- **PASS — MIR metadata consumer (static review):** validated HIR facet plans
  survive normal/bootstrap MIR lowering, optimizer/debug/AOP reconstruction,
  VHDL aggregation, and deterministic versioned JSON serialization. Direct HIR
  ownership edges now drive production `E-AF001` checks.
- **PASS — focused maintainability remediation:** type-predicate projection
  moved to `hir_lowering/type_predicate_projection.spl`; the oversized
  pre-existing `module_surface.spl` no longer carries feature additions.
  Other touched legacy compiler owners remain above 800 lines and require
  extraction or an explicit existing-owner exception before release.

## Release-blocking failures

- **FAIL — self-hosted runtime gates:** the retained full pure-Simple CLI exited
  `139` for `check src/compiler`, `check src/lib`, `check src/app/mcp`, and
  `check src/app/simple_lsp_mcp`. Focused feature probes likewise previously
  exited `139` or failed the deployed runtime ABI guard. No Rust-seed fallback
  or retry was used.
- **FAIL — fresh bootstrap gate:** the bootstrap-only Rust authority built, but
  the bounded pure-Simple Stage 2 attempts did not produce a compiler. Fix
  cycles exposed and repaired `extends` as a reserved field plus invalid
  predicate-parser generated names; the final attempt reached the linker and
  failed on unsupported `is_alnum`. That call is now rewritten to supported
  `is_alpha`/`is_digit`, but the mandatory three-cycle cap forbids another run
  in this session, so the repair is static-only evidence.
- **FAIL — MCP integration evidence:** the sole final invocation was malformed
  before the runtime started (`timeout` received `SIMPLE_LIB=src` as a command),
  so no passing MCP integration result exists; the no-retry guard was honored.
- **FAIL — generated manuals:** docgen for the static/root pair exited `139` in
  its lane; docgen for the pack/catalog pair exited `139` at final verification.
  The checked-in readable manuals therefore cannot satisfy the required
  pure-Simple `0 stubs` generated-manual gate.
- **FAIL — SSpec maintenance:** the deployed full CLI does not expose
  `sspec-maintain`; each required scan returned `ERROR: file not found:
  sspec-maintain`, so seven-component scorecards are unavailable.
- **FAIL — remaining executable/runtime integration:** source-level activation,
  binding lookup, generation leases, cache pinning, unload, mission policy, ABI
  identity, and MIR metadata are implemented, but no fresh pure-Simple runtime
  has executed them. The compiler driver still lacks one canonical
  `ModuleResolver` construction seam for automatic aspect-registry installation;
  SHB/SMF emission and witness-call lowering do not yet consume the MIR facet
  metadata; dynamic advice slots/patchpoints remain unimplemented.
- **FAIL — missing NFR evidence:** no retained startup/RSS/page-fault or
  first-use/lookup p50/p95/p99 baseline exists; NFR-AF-003, NFR-AF-005,
  NFR-AF-006, and NFR-AF-007 have no complete executable trace.
- **FAIL — coverage/build proof:** the declared 70–80% coverage annotations are
  not backed by a successful coverage run. The focused `module_surface.spl`
  regression was fixed, but touched legacy `module_loader.spl`,
  `module_lowering.spl`, and `hir_types.spl` remain above the preferred limit,
  and the new source paths still lack executable compiler/test evidence.

## Warnings

- The numbered-artifact working guard reported OK, but its Git-based staged
  probe cannot inspect this jj-only workspace; no staged jj change exists.
- Typed facet acquisition is reachable through the `std.aop` facade as explicit
  free functions. Proposed method sugar has no lowering yet.

## Result

**STATUS: FAIL** — the source implementation and focused executable specs are
substantially complete, but release/merge remains blocked by the self-hosted
runtime crash, missing generated-manual/runtime evidence, remaining driver and
backend integration, and absent NFR measurements. The WIP feature bookmark may
be committed/rebased/pushed for collaboration; no version bump, main push, tag,
or release is authorized by this report.
