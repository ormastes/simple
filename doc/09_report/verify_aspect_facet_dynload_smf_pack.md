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
- **PASS — explicit MIR call-unwind plumbing (static review):** every scanned
  `CallTerminator` constructor and pattern now carries the required
  `MirCallUnwindContract`; contradictory `NoUnwind`/edge and
  `MayUnwind`/no-edge pairs have canonical rejection tests. Deterministic JSON,
  representative optimizer preservation, backend/interpreter consumption, and
  live-facet unknown indirect-call `E-AF007` are covered by non-placeholder
  static specs. No compiler or backend was executed for this evidence.
- **PASS — typed HIR unwind owner and MIR admission (static review):** source
  `@may_unwind`/`@no_unwind` declarations populate the typed effect row;
  unannotated declarations default to `NoUnwind`; callable registration,
  type inference, imports, and method resolution preserve the row. MIR admits
  `NoUnwind` and rejects `MayUnwind`, missing, or conflicting metadata before
  call emission when no cleanup successor exists. Live facet scopes retain
  `E-AF007` precedence. This is static acceptance, not executable evidence.
- **PASS — explicit Throw/Resume groundwork (static review):** MIR owns
  payload-carrying `Throw` and `Resume` terminators with canonical builder and
  deterministic JSON forms. HIR `throw` no longer takes the unsupported-expression
  fatal path; with nested live facet leases it emits reverse-order, exactly-once
  releases before `Throw`. Unsupported backend/interpreter consumers reject the
  new terminators with typed `E-MIR-UNWIND002`. The static call path now builds
  a `MayUnwind` cleanup successor with one unwind-only landing pad, nested
  reverse releases, and terminal `Resume` of the original non-forwarded
  `ExceptionToken` on every unwind path; the optimizer release
  gate validates every function before and after transformation. Visitors and
  auxiliary type mappers no longer silently drop the token/destination. The
  verifier rejects external entries, cycles, non-resuming paths, token
  forwarding, and unknown cleanup opcodes. This does not prove executable
  behavior, source exception-packet identity, or a backend personality implementation.
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
- **PASS — lifecycle/ABI shape (static review):** the application gate,
  prepared callback-safe split, exact lazy reserve/I/O/commit, facet lifecycle,
  ordinary unload, embedding pack-I/O port, and facet/prepared compiler ABI
  leaves are wired without duplicate startup symbols or transition cycles. The
  runtime owner is 786 lines and its lifecycle source guard passes. This is not
  executable or concurrency evidence.
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
  or retry was used. The later standalone backend-owner crash is tracked in
  [`codegen_standalone_check_sigsegv_2026-08-04.md`](../08_tracking/bug/codegen_standalone_check_sigsegv_2026-08-04.md);
  it blocks executable admission of the new `CodegenPipeline` exception-CFG
  choke point despite passing focused MIR validation specs.
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
- **FAIL — executable backend/runtime evidence:** typed facet adapters, exact
  descriptor ABI wrappers, prepared v2 ordinary-call rewriting, and the stable
  prepared dispatcher ABI are implemented in source. Obsolete claims that
  these adapters or injection paths are missing are removed. No admitted
  current-source self-host/backend run proves generated calls, native callback
  dispatch, ABI linkage, or cleanup behavior, so AC-11 is not executable-
  verified.
- **FAIL — lifecycle and lease evidence:** sequential source/unit coverage does
  not prove concurrent acquire/unload, dispatch/unload, follower coalescing,
  callback-error cleanup, stale lazy commit rejection, completion-notification
  failure, or mismatched-claim drain. Leaf-level lease visibility and imported/
  indirect unwind handling remain unresolved; the required concurrency/resource
  model evidence is absent.
- **FAIL — deployment and startup configuration:** the embedding pack-I/O port
  contract exists, but production image-relative port/signature provisioning,
  application startup composition, feature/config enablement, and packaged ABI
  linkage have no retained deployment evidence.
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

**STATUS: FAIL** — catalog/artifact handling, typed facet adapter and ABI,
prepared v2 rewriting and ABI, the application gate, callback-safe split,
exact lazy reserve/I/O/commit, facet lifecycle, unload, and the embedding port
contract are implemented statically. Explicit MIR call-unwind metadata,
validation, serialization, representative optimizer preservation, backend
consumption, and payload-carrying Throw/Resume with direct leased-throw cleanup
are also implemented statically; they are not release evidence.
Blocking gaps are current-source compiler/backend execution and ABI linkage;
executable parser/import/method effect propagation; executable call-site
`MayUnwind` cleanup/payload preservation through `Resume`; async cancellation and cross-thread
unwinding; LLVM C API `invoke`,
landing-pad, and `resume` integration; production
deployment and startup configuration; lifecycle-wide concurrency, callback-
error, stale-commit, and lease-drain evidence; imported/indirect unwind and
leaf-level lease visibility; generated manuals; coverage; and retained NFR
measurements. The WIP bookmark may be synchronized for collaboration, but no
version bump, main push, tag, or release is authorized.
