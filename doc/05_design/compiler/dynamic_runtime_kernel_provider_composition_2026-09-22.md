<!-- codex-design -->

# Dynamic runtime/kernel provider composition — integration detail design

Status: dated addendum to existing selected provider plans; no implementation
completion claim. Source [architecture](../../04_architecture/compiler/dynamic_runtime_kernel_provider_composition_2026-09-22.md).
No UI surface is added. Aspect acquisition/signing/compression choices remain
with their existing options, not implicitly selected by this addendum.

## Frozen interface vocabulary

| Existing authority | Stable vocabulary | Integration obligation |
|---|---|---|
| Shared kernel contract | `IfaceId`, `ParamHeader`, `ParamExt` | Never invent an alternate ABI identity or expose private layouts |
| Composition | `SimpleCompositionImageV1`, `SimpleProviderQueryV1`, `SimpleProviderQueryResultV1` | Preserve existing wire sizes; version extensions explicitly |
| Full digest | `SimpleAbiDigest256V1`, `KpfDigest256` | Retain all 256 bits for identity checks; legacy u64 fields are not trust proofs |
| Provider session | `ProviderAdmissionRequestV1`, `ProviderLoaderSessionV1` | Admission binds mapping; a cached operation table is generation-pinned |
| KPF | `KpfGenerationHandle`, `KpfPinHandle`, `KpfSmfAdmissionReceiptV1` | One owner publishes/drains/retires a generation |
| Environment variants | `EnvironmentSnapshotV1`, `VariantDescriptorV1`, `BindingPlanV1` | Exact host eligibility differs from generated target intent |
| Aspect execution | `AspectDynloadExecutionLeaseV1`, `ApkFinalUnpinLeaseV2` | Bridge existing mapping owner and registry, never mint proof from counters alone |

The integration adds no new public ABI merely to combine these records.
Receipt projections must carry source owner/generation identity and full
artifact/dependency digests. If an existing wire cannot express these, author
and review a versioned extension before changing its producer or consumer.

## Bootstrap runtime closure

1. Resolve the actual runtime library the candidate will load, along with the
   static runtime inputs and exact selected dependency set.
2. Admit them into the immutable bootstrap generation; record target/format,
   full bytes hashes, exports/ABI, producer and disposition (static/dynamic).
3. Make candidate link/run paths use that admitted generation. Never search a
   mutable build directory or accept archive hash equality as cdylib equality.
4. Verify admitted identity immediately before execution through the canonical
   bootstrap owner. A missing/changed required cdylib is an authority error.
5. A provider-only edit invalidates its capsule/receipt; preserve unaffected
   compiler object caches where dependency evidence proves independence.

This P0 repair is owned by the bootstrap lane. This document does not rewrite
its scripts, authority schema or in-flight generation.
The confirmed owners are `scripts/bootstrap/bootstrap-from-scratch.sh`,
`scripts/bootstrap/bootstrap-authority-wiring.shs`,
`scripts/bootstrap/phase2-runtime-capsule.shs`, and
`scripts/check/lib/bootstrap-stage3/authority.shs`. Target-aware dynamic fields
may preserve legacy static-only compatibility only when that composition makes
no required dynamic-provider claim; absence is never success for dynamic mode.

## Runtime and Cocoa loading

Metadata discovery records the exported capability without library load or UI
initialization. First Cocoa demand asks the runtime provider owner to resolve
the exact admitted provider. The owner checks platform/ABI/identity and loads
once, resolves the required `rt_cocoa_*` table from its handle, prepares domain
state and publishes the table atomically. A missing symbol rejects the whole
required interface with a typed error; partially initialized tables are hidden.
The static executable contains no competing Cocoa implementation. Runtime core
trampolines and GUI framework implementation remain separate responsibilities.

The current Cocoa lane attaches `hosted_cocoa.c` through a cdylib-only link
argument and resolves its exact 12 registered signatures through
`DynamicSymbolProvider`. Qualification checks that runtime `rlib`/`staticlib`
and native-all archives contain no implementation definitions, while the
standalone `libsimple_runtime.dylib` exports all 12 with correct signatures.
Feature selection alone is insufficient because the three Cargo crate outputs
share a feature graph. Retain this scoped mechanism while proven; consider a
separate provider artifact target only when independent packaging is warranted.
Resolve the observed LLVM 23 `ld64.lld` Objective-C dispatch-stub incompatibility
with a qualified compiler/linker combination and retain its exact provenance.

GUI events/callbacks hold generation leases. AppKit thread-affinity constraints
remain enforced by the UI owner. A failed or unsupported unload keeps the
mapping retained and reports the outcome; it cannot manufacture a release.
Linux/FreeBSD/Windows adapters use the same semantic interface but their own
admitted artifact format and loader; extension spelling is not format proof.

## Admission, commit and error behavior

Bound all manifest bytes/records, dependency depth, sessions and outstanding
loads. Reject cycles where unsupported, duplicate IDs, offset/size overflow,
unknown mandatory fields, capability escalation and incompatible interfaces.
Join immutable dependency-lock identity before mapping. Native dependency
resolution must be pinned or constrained sufficiently to bind the actual
loaded closure; otherwise return an admission error before invoking code.

Load states remain `Declared -> Admitting -> Loading -> Verifying -> Ready`
or `Rejected`, projected into the existing KPF generation states. Publish only
after all required operations and resource initialization succeed. Failure
cleans private candidate state and retains the active generation. Capture phase,
provider, full digest, target, generation and stable reason in bounded receipts.

Single-flight waiters observe one admitted result with a native happens-before
edge. Lifecycle serialization belongs to the existing loader owner; no copied
Simple value handle may independently mutate the authority. The steady call
holds a generation pin and invokes its dense slot directly. A retired or
cross-generation handle rejects; it never resolves again by ambient symbol name.

## Aspect integration

Reuse the existing typed facet/binding-plan and mapping-receipt owner bridge.
Activation requires ABI-compatible callable payload, authenticated/admitted pack
identity under the selected policy, mapping provenance, registry generation and
execution lease. Test payloads must produce a distinguishable result from their
own mapped code; a host callback gated by metadata is not a loaded advice body.

Quiescing closes new admission, waits for calls/around continuations/callbacks/
device fences, and performs final-unpin/release through the canonical loader.
Physical unmap is a distinct platform result. Until that bridge is proven,
report retained mapping/unsupported retirement, not completed unload.

No transparent loading syntax is added. Existing options retain decisions on
resident/no-I/O composition, lazy versus explicit acquisition, authentication,
compression and lifecycle policy. Static weaving still invalidates compiled
consumers; dynamic generations never rewrite a static call plan invisibly.

## Evidence schema and measurements

The evidence join records host/compiler/tool hashes; composition and manifest
digest; provider/dependency digests; target and ABI; selected versus executed
provider; generation/pin/mapping identity; reject/publish/close status; phase
timings; mapped text and max RSS. Record unsupported platform rows explicitly.

Startup fixture: no-import hello and representative MCP/LSP startup with zero
optional UI/GPU providers. Demand fixture: one Cocoa or GPU capability with no
unrelated providers. Dispatch fixture: pinned coarse batch versus same direct
batch. Invalidation fixture: body-only, ABI, dependency and policy mutations.
Retain separate first-use and warm measurements; do not blend failed admission
or fixture-only probes into native execution/performance claims.
