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
  `around`. The config-gated producer now emits automatic phase-specific MIR
  dispatch intrinsics; executable backend dispatch is still unclaimed.
- **PASS — retained NFR harness shape (static review):** a real SFM2/ordinary-SMF
  fixture builder and native probe cover cold construction, first activation,
  exact-generation facet method acquisition, native receiver-shaped invocation
  while the lease is held, lease release, and real loader-owned advice dispatch;
  both native paths must return exactly `73`. The build/collector require exact
  compiler-to-probe plus v2 probe-contract provenance, and the probe reports
  facet receiver dispatch as `verified` only after the resolved ordinary-SMF
  method executes successfully. A lookup-only run cannot masquerade as call
  evidence.
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
  predicate-parser generated names; the final local attempt reached the linker
  and failed on unsupported `is_alnum`. Current source has removed that call,
  and rebased main adds packed/raw bootstrap return-local repairs. Separate
  retained ARM64 recovery evidence subsequently reached functional admission
  with a Stage-2 candidate but produced a truncated 104-byte LLVM module; it is
  not Linux admission evidence. This workspace still has no current-source
  Linux Stage-2/3 provenance or admitted self-host, and the mandatory local
  three-cycle cap forbids another run in this session.
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
- **FAIL — production language/advice execution remains incomplete:** facet
  implementation bodies lower as ordinary HIR/MIR functions under
  `<implementation>__facet_witness__<method>`; `self.base` uses the explicit
  base-as-argument-zero ABI, while unsupported bare `self` fails with E-AF005.
  Artifact v3 carries an inert `FacetWitnessDescriptorV1` identity plus ordered
  method symbols. The loader resolves every method to the exact SMF owner and
  address, publication stores that resolved descriptor, and application
  acquisition returns a method entry with its exact generation lease. No
  executable factory or parallel private invoke ABI remains. The explicit
  runtime and native probe can invoke this receiver-shaped method path, but
  user-facing type-directed facet-method sugar, inherited table flattening, and
  generic facet descriptors still fail closed. Review also proved the current
  public `FacetRef<T>` stores only diagnostic text, a caller-supplied view, and
  lease IDs: it is not the documented dynamic typed adapter. Production needs
  a compiler-generated private `(Base, FacetContract)` adapter with the typed
  base, complete resolved descriptor, and an affine lease bound to the exact
  application execution context. Existing `dyn Trait` has no usable native
  vtable path and raw/`Any` base erasure is unsafe. Dynamic advice has a canonical
  projection dispatch boundary with exact-generation pin/release and rejects
  runtime `around`; automatic prepared-slot MIR calls still lack a backend-safe
  route to that application-owned boundary, so AC-11 remains unmet.
- **FAIL — prepared join-point backend bridge incomplete:** `MirModule` contains
  a versioned `PreparedAdviceSlotPlan` table that survives current MIR
  reconstruction/optimization/VHDL aggregation and has deterministic serializer
  plus driver collection. `CompileOptions.prepared_dynamic_advice` derives slots from
  the established weave authority and inserts automatic entry/return/abort MIR
  phase calls. The loader derives an immutable projection from canonical
  publication, installs it atomically with lifecycle promotion, invalidates it
  before quiesce/drain, and pins/releases every exact generation on all dispatch
  paths. An executable backend trampoline still does not exist. The option participates in cache identity;
  check/interpreter reject it directly and JIT/all AOT backends reject produced
  tables centrally with `E-AF010`; the common backend compiler independently
  rejects either slot metadata or the intrinsic if a caller bypasses the driver.
  A focused unit gate enumerates every supported backend spelling and also
  constructs an intrinsic-only module, proving both metadata and direct-call
  paths reject before backend selection/lowering. The current `(slot, phase)`
  intrinsic cannot prove the canonical lease, and the reviewed architecture
  rejects process-global/current-context handles as a second authority. AC-11
  remains unmet. The reviewed successor is
  `simple.prepared_advice_dispatch.v2(context, slot, phase)`, accepted only for
  a target with one exact typed `AspectExecutionContext` parameter. A driver
  pass must rewrite validated v2 to the ordinary source-owned
  `prepared_advice_dispatch_context_invoke` call, and every residual v1/v2 must
  remain a backend error. Before that can execute, one stable reference capsule
  must solely own the loader, lifecycle, registries, and projection; copied
  coordinator state is not safe. Hosted CPU AOT entry-closure is the first
  proposed admission surface; all others remain fail-closed.
- **FAIL — missing NFR evidence:** the admitted builder/probe/collector now
  exist, but no retained startup/RSS/page-fault, opened-file, first-use, or
  repeated-lookup baseline has executed. The one-byte disabled-slot value is
  explicitly a contract minimum, not the NFR-AF-003 backend footprint
  measurement. The fixture can now prove an exact native advice result, but
  the facet-call proof and all NFR baselines remain unexecuted because the
  deployed pure-Simple compiler/runtime is unavailable. NFR-AF-003,
  NFR-AF-005, NFR-AF-006, and NFR-AF-007 remain incomplete.
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

**STATUS: FAIL** — the earlier catalog/artifact and D1/D2 source slices,
automatic registry integration, advice publication, and retained NFR harness
are substantially complete. D4 now has the stable execution-context owner,
typed v2 production/validation, fail-stop ordinary-call rewriting, isolation,
cleanup, entry-closure, residual-intrinsic, and coverage checks. D5 now has
genuine source/HIR acquisition, application-owned opaque descriptor leases,
exact nominal context/contract proof, canonical ordinal/signature resolution,
checked context-first method-address lookup, typed-base indirect-call lowering,
and HIR-symbol lambda/async capture rejection. Wrapper-aware adapter provenance
and reverse-order cleanup now cover every currently modeled lexical exit.
Exact-route lazy activation and canonical `FacetAcquireError` are now wired;
unsupported leased nonlocal exits fail closed with E-AF007. Release/merge
remains blocked by production image/signature port binding, lifecycle-wide
concurrency beyond lazy callers, indirect/imported and backend unwind support,
leaf-level lease visibility, the self-hosted runtime crash,
missing generated-manual/runtime evidence, executable prepared-advice backend
evidence, the intentionally unselected lexical-context shorthand, and absent
NFR measurements. The WIP feature bookmark may
be committed/rebased/pushed for collaboration; no version bump, main push, tag,
or release is authorized by this report.
