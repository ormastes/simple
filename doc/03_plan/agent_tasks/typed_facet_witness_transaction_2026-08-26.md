# Typed Facet Witness Transaction — Implementation Handoff

**Status:** blocked on contract acceptance and prerequisite ownership  
**Merge owner:** aspect dynload parent lane  
**Final reviewer:** xhigh static reviewer, then production verification only
when implementation is explicitly authorized

## Shared names

All implementation lanes use these names from the architecture contract:

- `ConcreteTypeIdV1`, `FacetInterfaceIdV1`, `FacetMethodIdV1`
- `FacetImplIdV1`, `FacetBindingIdV1`
- `FacetIdentityEncodingV1`, `ApplicationCatalogAdmissionProofV1`
- `FacetMinimumTrustPolicyV1`, `ApkTypedFacetAdmissionLeaseV1`
- `FacetContractAbiHashV1`, `FacetMethodSignatureHashV1`,
  `FacetImplAbiHashV1`
- `FacetAdmissionProofV1`, `FacetWitnessHeaderV1`
- `FacetWitnessBindingV1`, `FacetWitnessMethodV1`
- `ModuleLoadTransactionV1`, `FacetRef<T>`
- `FacetCallableAbiV1`, `FacetVTableV1`, `FacetStateScopeV1`
- `HirFacetAcquireMode`, `HirFacetInterfaceRef`, `FacetMethodResolutionV1`
- `HirExprKind.FacetAcquire`, `MirFacetCallAbiV1`, MIR `FacetAcquire`,
  MIR `FacetInvoke`, MIR `CallIndirectAbi`, `FacetExecutionGuardV1`

No lane substitutes text IDs, payload casts, ambient globals, hardcoded success,
or placeholder assertions for these contracts.

## Dependency order and ownership

1. **Requirements owner:** select/finalize the typed-facet language requirement,
   `FacetAccess`/`BindOption` grammar, access annotation spelling, and critical
   diagnostic scope. No code lane may invent these decisions.
2. **Identity/trust owner:** add the one canonical SHA-256 binary encoder, opaque
   four-`u64` identity newtypes, authenticated application-catalog proof, and
   immutable non-downgradable loader minimum trust policy.
3. **Metadata owner:** add Catalog V3/ModuleEntry V4 fixed IDs, content hashes,
   signature-policy provenance, and exact `.facet_witness` binding/method/
   callable ABI/state-scope registration across Simple/Rust readers and writers.
4. **Mapping owner:** deliver rollback-safe staged map/relocate/seal/unmap and
   address-ownership queries. Publication is outside SegmentMapper.
5. **Loader owner:** add the immutable aspect admission lease, explicit
   execution-context loader capability, binding/per-object single-flights,
   authoritative one-record transaction/registry, exact state-scope factory
   rollback, sidecar ownership, public pins, activation/invocation guards, and
   ordered unload/quarantine.
6. **Compiler metadata owner:** emit SHB facet contracts and concrete runtime
   descriptors with stable fixed IDs and ABI/layout hashes.
7. **Frontend owner:** add the dedicated parser/AST/HIR nodes,
   `MethodResolution.FacetMethod` with complete schema/consumer updates, and
   exact type/effect rules only after owners 2-6 expose accepted interfaces.
8. **MIR/backend owner:** add typed acquisition/invocation lowering and implement
   `MirFacetCallAbiV1`, `lower_facet_abi_ops`, absence verification, and
   `CallIndirectAbi`; every optimizer/backend/interpreter must preserve it or
   reject it explicitly, including the current native x86_64 gap.
9. **Spec owner:** implement the non-vacuous plan in
   `doc/03_plan/sys_test/typed_facet_witness_transaction_2026-08-26.md` and only
   then activate the pending REQ-APK-P04 source acceptance.
10. **Merge owner:** reconcile interfaces, perform the authorized verification
   once, and request final highest-capability review.

## Parallelization

After requirements are selected, identity/trust, metadata, mapping, and compiler
metadata may proceed in parallel after freezing their shared wire names. Loader
depends on identity/trust, metadata, and mapping. Frontend depends on compiler
metadata and accepted loader entry points. MIR/backend depends on loader and
frontend. Specs may create fixtures alongside each owner but
must not activate source acceptance early.

## Stop conditions

Stop and return to design if any implementation would require:

- treating CRC32, a name, or an unsigned policy verdict as authentication;
- accepting a catalog that is not rooted in application authority or that
  weakens the loader's out-of-band minimum trust policy;
- representing any typed identity as variable-length bytes/text or using a
  noncanonical encoder;
- publishing aspect-pack state before mapped witness validation;
- performing a second typed registry commit instead of transferring one
  immutable admission lease into the authoritative loader record;
- changing a base object's layout at runtime;
- looking up a method name on every call;
- parsing/splitting a text facet key in the typed hot path;
- using process-global loader state;
- losing facet slot/method/signature identity between HIR method resolution and
  MIR `FacetInvoke`;
- calling a per-object factory or facet method without an internal
  exact-generation execution guard that unload also waits for;
- lowering to ordinary `CallIndirect` without the explicit facet call-ABI
  descriptor or letting an optimizer discard that descriptor;
- unmapping code before sidecar destruction or while a generation is pinned;
- claiming native support while `CallIndirectAbi` is rejected;
- satisfying a spec with pending/vacuous assertions.
