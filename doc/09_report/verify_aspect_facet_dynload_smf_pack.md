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
- **PASS — documentation reconciliation (static):** requirements, architecture,
  detail design, test plan, continuation agent plan, system-manual scenario
  counts, and executable-source hashes were reconciled with this source slice.
  Pure-Simple docgen evidence remains unavailable and is listed below.
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
- **PASS — automatic registry source path (static review):** real compile inputs
  discover and install the resolver-owned aspect registry; its fingerprint is
  carried into object/closure cache identity. Importer-scoped resolution keys,
  per-importer closure authorization, and explicit hidden-root checks prevent
  an aspect importer from authorizing later business imports.
- **PASS — artifact metadata boundaries (static review):** SHB v1.1 carries
  versioned facet contracts with v1.0 compatibility; ordinary SMF carries
  deterministic `.facet_bindings` records. UTF-8 byte lengths and bounded
  record counts are enforced, corrupt SHB/SMF metadata fails closed, and a
  facet-bearing catalog cannot publish a legacy SMF without binding metadata.
- **PASS — advice publication source slice (static review):** the loader-owned
  registry validates prepared slots, sorts by content rather than native text
  pointer order, publishes/unbinds exact generations, and exposes lookup and
  disabled-path counters through the application owner. Its explicit
  `advice_dispatch_slot` seam validates the complete matching phase against the
  loader before zero-argument before/after invocation and rejects dynamic
  `around`; no automatic MIR/backend business-path caller is claimed.
- **PASS — retained NFR harness shape (static review):** a real SFM2/ordinary-SMF
  fixture builder and native probe cover cold construction, first activation,
  published-facet lease lookup/release, cache/advice counters (including
  dispatch attempts, invocations, failures, and rejected `around` advice), and
  per-mode opened files. The build/collector require exact compiler-to-probe
  provenance and mark the first record `collected-not-thresholded`.
- **PASS — continuation static gates:** shell syntax, changed-file placeholder,
  conflict-marker, and trailing-whitespace scans passed; generated-spec `.spl`
  count is `0`; both final direct-env/runtime guards report `STATUS: PASS`.
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
- **FAIL — production witness/advice execution:** metadata emission and loader
  publication exist. Receiver-independent facet implementation bodies now
  retain AST/HIR metadata and lower as ordinary HIR/MIR functions under
  `<implementation>__facet_witness__<method>`; receiver-dependent `self` and
  `self.base` bodies fail closed with E-AF005 rather than being rewritten.
  Lowering still does not produce the emitted `<implementation>__facet_witness`
  factory symbol or export a method table, and no production caller
  invokes `lower_resolved_facet_witness_call`. Facet artifact production now
  fails closed with `E-AF002` unless that canonical symbol is proven present in
  the emitted ordinary-SMF symbol set; emitted witness-method functions do not
  masquerade as that missing factory. Dynamic advice now has an explicit
  `advice_dispatch_slot` boundary that revalidates loader owner/address and can
  invoke zero-argument before/after witnesses; runtime `around` is rejected
  without a real proceed continuation. No production prepared-slot MIR caller
  or safe executable callback evidence exists, so AC-11 remains unmet.
- **FAIL — no production prepared join-point producer:** `MirModule` contains
  a versioned `PreparedAdviceSlotPlan` table that survives current MIR
  reconstruction/optimization/VHDL aggregation and has deterministic serializer
  plus driver collection. No syntax/config producer, backend table encoding, or
  business-path caller exists; native/SMF emission therefore rejects non-empty
  tables with `E-AF010`. `mir_aop_injection.spl` still emits direct static advice
  calls only. AC-11 remains unmet.
- **FAIL — missing NFR evidence:** the admitted builder/probe/collector now
  exist, but no retained startup/RSS/page-fault, opened-file, first-use, or
  repeated-lookup baseline has executed. The one-byte disabled-slot value is
  explicitly a contract minimum, not the NFR-AF-003 backend footprint
  measurement. NFR-AF-003, NFR-AF-005, NFR-AF-006, and NFR-AF-007 remain
  incomplete.
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
- The resolver dependency inversion is closed: layer 80 consumes the injected
  `ModuleResolverDiscoveryPort`, production CLI/backend composition installs the
  99-loader adapter, and compatibility plus test-only constructors explicitly
  select empty/no-registry behavior. Static import audit finds no
  `compiler.loader` dependency beneath `src/compiler/80.driver`.
- Direct in-process compatibility APIs retain their historical signatures and
  delegate to an explicit empty discovery port. Injected variants exist for
  interpreter, C, native single-file, project, and focused-bootstrap paths.
  Application callers that enter those in-process paths use the injected
  variants; subprocess-based public helpers enter the already-injected app CLI.
  The historical `src/compiler/80.driver/main.spl` source entry and unused
  bootstrap/driver API compatibility wrappers remain intentionally
  no-registry because importing the 99 adapter there would recreate the layer
  inversion. The shipped application CLI is the aspect-aware composition root.
- Touched legacy owners remain above the preferred size: `compile_targets.spl`
  (1370), `driver_source_loading.spl` (1095), and HIR lowering `types.spl` (826).

## Result

**STATUS: FAIL** — the source implementation, automatic registry integration,
artifact codecs, advice publication, and retained NFR harness are substantially
complete, but release/merge remains blocked by the self-hosted runtime crash,
missing generated-manual/runtime evidence, production witness/advice dispatch,
receiver/backend preparation gaps, and absent NFR measurements. The WIP feature bookmark may
be committed/rebased/pushed for collaboration; no version bump, main push, tag,
or release is authorized by this report.
