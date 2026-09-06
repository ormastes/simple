# Typed Facet Witness Transaction Test Plan

**Status:** design only; executable specs intentionally not added before the
loader/witness contract is implemented.

No case below may use `pending_skip`, `pass`, `expect(true)`, existence-only
checks, or a zero-error assertion without inspecting the resulting node/state.

## Parser and AST

Target: `test/01_unit/compiler/frontend/facet_acquisition_parser_spec.spl`

- Parse all three source forms and assert exact receiver, mode, retained full
  type tree, zero value arguments, and full span.
- Round-trip the flat/canonical AST and assert the same fields.
- Reject `facet<>()`, `facet<A,B>()`, missing `>`, and any value argument with
  `E-AF-TYPE-001` and an exact span.
- Prove `a < b`, `obj.facet < rhs`, and ordinary `obj.facet()` keep their prior
  AST forms.

## HIR and typing

Target: `test/01_unit/compiler/hir/facet_acquisition_hir_spec.spl`

- Admit a real facet contract fixture and assert exact `HirFacetAcquire` mode,
  resolved symbol, instantiated type, fixed interface ID, and contract hash.
- Assert exact result types for resident/optional/required acquisition.
- Put each expression in a deliberately wrong annotation and require a type
  mismatch, proving the result is not an unconstrained fresh variable.
- Reject an unknown type, ordinary class, ordinary trait, unsealed facet, and
  ABI-inexpressible facet method with the documented diagnostics.
- Assert HIR codec/hash round-trip preserves mode and both 32-byte values.
- Resolve a facet method and assert exact
  `MethodResolution.FacetMethod` interface/method symbols, opaque
  interface/contract/method/signature IDs, and slot survive HIR codec,
  monomorphization, and MIR lowering. An `Unresolved` result is a failure.
- Assert `try_facet` carries no I/O effect; assert lazy forms are rejected in
  sealed critical context and accepted only with explicit capability.

## MIR and backend structure

Target: `test/01_unit/compiler/mir/facet_acquisition_lowering_spec.spl`

- Assert each HIR mode yields one typed `FacetAcquire` with receiver, explicit
  loader context, interface ID, and contract hash; no unresolved method call or
  source-name operand remains.
- For a known facet method, assert the declared slot and method/signature IDs,
  `MirFacetCallAbiV1` convention/pointer-width/ownership/effects/no-unwind fields,
  checked vtable load, and `CallIndirectAbi` exact `MirSignature`.
- Assert `lower_facet_abi_ops` removes every `FacetAcquire`/`FacetInvoke`,
  `verify_no_high_level_facet_ops` rejects an injected survivor, and the emitted
  `CallIndirectAbi` retains byte-identical ABI metadata through each optimizer
  that handles indirect calls.
- Change one ABI field at a time and require signature-hash verification failure;
  prove no transform degrades `CallIndirectAbi` to ordinary `CallIndirect`.
- Compile a wrong-slot/wrong-signature fixture through hardened lowering and
  require refusal before indirect execution.
- Every target and the HIR/MIR interpreters either execute a known indirect facet method result or emit the
  documented unsupported-target error; silent NOP/direct-byte paths fail.

## Witness decoder

Target: `test/01_unit/compiler/loader/facet_witness_decoder_spec.spl`

- Decode one canonical section and assert every header, binding, and method
  field plus every callable ABI record and exact vtable header/slot offset.
- Refuse bad magic/version/size, overflow, overlap, misalignment, nonzero
  reserved fields, unknown flags, zero/duplicate bindings, sparse/duplicate
  slots, duplicate method/callable/symbol IDs, undefined state scopes,
  inconsistent sidecar flags, and out-of-range callable/symbol indices.
- Refuse zero or multiple witness sections for a typed route.
- Refuse reordered, missing, extra, or signature-mismatched methods against the
  compiler contract.
- Refuse factory/destroy/method records whose authenticated callable kind,
  calling convention, pointer width, flags, signature hash, or recomputed symbol
  identity does not match.
- Mutate each `FacetImplAbiHashV1` input independently—state scope, access/layout
  hash, factory/destroy signature, method order/slot/flags, and callable symbol
  identity—and require mismatch against Catalog V3, ModuleEntry V4, witness, or
  loader recomputation before mapping/factory execution.

## Identity and trust authority

Target: `test/01_unit/compiler/loader/facet_identity_trust_spec.spl`

- Produce the same opaque ID independently from SHB and packer fixtures and
  assert all 32 bytes match the canonical SHA-256 vector.
- Reject non-NFC names, invalid module segments, unknown type tags, open generic
  variables, alternate length/count widths, overflow, trailing bytes, uppercase
  diagnostic hex, and cross-kind newtype substitution.
- Admit an application-signed catalog and prove its catalog digest is inside the
  verified application proof.
- Attempt to weaken required signature/trust-root/ABI policy in catalog and route
  fields; effective policy remains the strict loader minimum and admission is
  refused. Catalog-provided trust roots never authenticate themselves.
- Exercise independently pinned integrity-only development mode and assert it is
  reported as `integrity_only`, never signature-authenticated.

## Transaction fault matrix

Target: `test/01_unit/compiler/loader/typed_facet_transaction_spec.spl`

Inject one deterministic fault after each stage: route preparation, pack hash,
signature policy, module hash, SMF parse, witness parse, dependency resolution,
map, relocation, seal, address ownership, vtable construction, factory call,
catalog-generation recheck, and commit.

After every failure assert all of:

- tuple registry has no binding;
- global symbol/module counts are unchanged;
- no acquirable vtable or sidecar exists;
- generation did not advance;
- the immutable admission lease was released exactly once and no typed
  aspect-pack binding registry changed;
- every staged mapping was unmapped, or a cleanup fault produced an inaccessible
  quarantined owner that is not reusable;
- all counters changed only for work that actually occurred;
- the returned code and stage-specific diagnostic are exact.

Add an adversarial payload whose names/ABI strings match but whose fixed IDs or
content hash differ; it must refuse before factory execution.

## Acquisition and cache behavior

Target: `test/01_unit/compiler/loader/typed_facet_acquisition_spec.spl`

- First lazy acquisition maps one selected module, publishes one generation,
  invokes one factory, and returns a ref bound to the real receiver/vtable.
- Second acquisition of the same binding **and same receiver object** uses the resident tuple registry and
  causes zero catalog parses, hashes, pack-directory scans, decompressions,
  mappings, relocations, symbol-name scans, factory calls, and source reads. A
  distinct `PER_OBJECT` receiver is covered separately and runs one factory.
- `try_facet<T>` miss returns `None` with zero open/read/hash/decompress/map/
  factory/generation delta.
- `facet<T>` route miss is `Ok(None)`; `require_facet<T>` route miss is the exact
  required-facet error.
- A spoofed static type hint cannot override the receiver's concrete descriptor.
- Exercise `STATELESS`, `PER_BINDING`, and `PER_OBJECT`: stateless has zero
  sidecar; per-binding factory runs once with zero receiver handles; per-object
  factory runs once per distinct object/generation and reuses the instance for
  the same object.
- Concurrent first acquisition for a second object joins one per-object
  single-flight. Factory failure/deduplication destroys staged state, takes no
  pin, and yields `None` for `try_facet` versus an exact error for lazy forms.
- Catalog replacement invalidates by generation without scanning call sites.
- Concurrent first use joins one single-flight and observes one payload
  preparation, mapping, factory/instance creation, and committed generation.

## Pin and unload

Target: `test/01_unit/compiler/loader/typed_facet_unload_spec.spl`

- Copy a `FacetRef`, drop one copy, and prove the shared control remains callable
  and exactly one generation pin remains.
- Request unload with a live ref: state becomes `QUIESCING`, new acquisition is
  refused, the existing ref calls successfully, and no unmap occurs.
- Drop the last ref and assert exact order: destroy sidecar, remove instance,
  remove witness/symbol visibility, unmap, release admission lease, mark unloaded.
- A stale ref never becomes live after reload; the new binding has a distinct,
  never-reused generation.
- Destroy or unmap failure produces `QUARANTINED`, retains the mapping as
  inaccessible/non-reusable, and never reports unloaded.
- Catalog invalidation and loader destruction refuse while pins/quarantine live.
- Pause a later-object factory after it acquires its activation guard, request
  unload, and prove state quiesces but destroy/unmap cannot begin. Resume factory:
  it observes quiescence, destroys staged state, releases the guard, returns the
  exact acquisition failure, and only then may unload continue. No public pin or
  instance is published.
- Pause a facet method after it acquires its invocation guard, concurrently drop
  the last public ref and request unload, and prove code remains mapped until the
  call returns and releases its guard.

## Source-to-runtime acceptance

Only after the preceding unit/integration cases exist, replace the pending
REQ-APK-P04 source acceptance rather than adding a second placeholder. Compile
and execute source syntax through the production explicit `ModuleLoader`, route
the same fixed IDs as the direct catalog API, call a real facet method that
returns fixture-dependent data from the receiver, and assert all loader counters
and lifecycle states above.

The acceptance is not complete if it merely compiles, returns a hardcoded value,
or asserts that a function exists.
