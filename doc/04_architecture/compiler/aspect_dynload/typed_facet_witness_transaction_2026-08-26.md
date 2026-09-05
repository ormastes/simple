# Typed Facet Witness and Loader Transaction Architecture

**Status:** proposed prerequisite contract; not implemented  
**Date:** 2026-08-26  
**Base:** `03393d5f21ec8d2ad32b864197e9a3596fd2e80d`  
**Scope:** the `obj.try_facet<T>()`, `obj.facet<T>()`, and
`obj.require_facet<T>()` language surface in the aspect-pack lane

## Decision

Typed facets SHALL NOT be represented by `ApkFacetLoadV1.payload`, by a cast of
payload bytes, or by the existing `ModuleFacetRefV1`. A typed facet is published
only after an admitted ordinary-SMF payload has been mapped, relocated, sealed,
its authenticated witness descriptor has been checked against the catalog and
compiler contract, and its factory has succeeded inside one loader-owned
transaction.

The transaction owner is `ModuleLoader`. The aspect-pack container may prepare
and validate a route and selected payload, but it may not publish a typed binding
or advance a typed generation. The one authoritative committed record owns the
mapping, resolved symbols, immutable vtable, sidecar instances, provenance,
generation, and pins.

This is an architectural prerequisite, not a claim that `facet<T>` works. No
source syntax or runtime entry point may be advertised until the transaction,
witness ABI, and native indirect-call path below exist.

## Current-state evidence

The current production surfaces are useful compatibility foundations, but none
is a typed witness:

- `src/lib/common/aspect_pack.spl` routes text keys and returns
  `ApkFacetLoadV1`, whose executable content is a byte payload.
- `_apk_acquire_facet_body_opened` publishes an aspect binding after route and
  ABI checks, before an ordinary SMF is mapped or a witness is validated.
- `ModuleLoader.aspect_facet_visible` retains an indexed catalog and avoids
  reparsing it on a hot lookup, but returns the same payload result.
- `ModuleFacetRefV1` pins a byte-binding generation and explicitly disclaims
  compiler `facet<T>` lowering. It has no base reference, vtable, or sidecar.
- ordinary `ModuleLoader.load_with_intent` maps and publishes symbols, but does
  not offer a rollback-safe staged symbol/mapping transaction for a facet.
- `rt_vtable_lookup` traps because the current emitter supplies no authenticated
  vtable identity. Facet dispatch therefore cannot reuse that path.
- MIR has `CallIndirect`; the native x86_64 selector currently rejects it.

## Non-negotiable invariants

1. **No typed bytes.** Payload bytes never become `FacetRef<T>` by cast,
   interpretation, name lookup, or caller assertion.
2. **One authority.** Only `ModuleLoader` publishes and retires typed bindings.
3. **Authenticated provenance.** A witness descriptor is accepted only from the
   exact module payload selected by a validated catalog route, with the payload,
   pack, route, and signature-policy verdict retained in an admission proof.
4. **No partial visibility.** A transaction failure leaves no acquisition row,
   symbol, method table, sidecar, pin, mapping, or generation visible.
5. **W^X.** Relocations happen while staged segments are writable. Executable
   pages are non-writable before any factory or facet method executes.
6. **Typed dispatch.** Interface, concrete type, method, signature, and binding
   identities are fixed-size typed values. Delimiter-split text keys are not an
   authority for the typed path.
7. **No hot-path parsing or scans.** Resident acquisition is an exact tuple-map
   lookup and a pin; a new per-object sidecar may additionally run its admitted
   no-I/O factory. It performs no I/O, content hashing, decompression, catalog parsing,
   pack-directory scan, symbol-name scan, mapping, or source scan.
8. **Exact generation pins.** A `FacetRef<T>` pins one binding ID and generation.
   A later generation can never revive a released or stale reference.
9. **Fail closed.** Missing, duplicate, malformed, unsupported, mismatched, or
   unauthorised metadata refuses the transaction with a stable diagnostic.
10. **Compatibility isolation.** Existing text/payload APIs keep their public
    behavior. They are not implementation shortcuts for the typed surface.

## Typed identity contract

All runtime identities below are SHA-256 results: exactly 32 raw bytes on the
wire and four little-endian `u64` words in memory. Each public identity is a
distinct opaque newtype with private words and one validating constructor; none
is an alias of `[u8]`, `text`, or another identity. This representation is used
unchanged by SHB, Catalog V3, ModuleEntry V4, witness records, HIR, MIR, cache
keys, and runtime registries.

Hex text is allowed only at a CLI/diagnostic boundary. A decoder accepts exactly
64 lowercase ASCII hexadecimal characters, decodes them into the opaque type,
and rejects all other forms. It is never used to recreate an ID on a hot path.

### `FacetIdentityEncodingV1`

Every ID preimage uses this binary envelope before SHA-256:

```text
magic[8] = "SFIDENC1"
domain_length:u32-le
domain:utf8
component_count:u32-le
repeat component_count:
    component_length:u64-le
    component_bytes
```

Strings are valid UTF-8 normalized to NFC. Package identity is the 32 raw bytes
of the admitted lockfile/package-content hash. Module identity is a `/`-separated
logical path with NFC segments; empty, `.`, `..`, repeated separator, leading
separator, and trailing separator are invalid. Declaration identity is its
compiler-assigned SHB serial encoded as `u64-le`, scoped by package and module;
source names are retained only as a diagnostic component and use NFC bytes.
Counts and lengths are canonical fixed-width values. Decoders reject overflow,
trailing bytes, or alternate encodings.

The SHB serial is assigned by the versioned canonical declaration traversal,
persisted in SHB, and reproducible for identical admitted inputs. Renumbering is
an ABI change and changes the declaration/type/facet IDs; filesystem enumeration
order, hash-map order, and process-local symbol numbers are forbidden inputs.

Recursive concrete type arguments use this byte grammar:

```text
type := 0x01 builtin_code:u16-le
      | 0x02 nominal_decl_id[32] arg_count:u32-le
             repeat arg_count: type_length:u64-le type
      | 0x03 tuple_count:u32-le
             repeat tuple_count: type_length:u64-le type
      | 0x04 immutable_ref type_length:u64-le type
      | 0x05 mutable_ref type_length:u64-le type
      | 0x06 array length:u64-le type_length:u64-le type
```

Builtin codes come from the versioned SHB ABI builtin registry, not an enum
ordinal. V1 rejects functions, inference variables, open generic parameters,
aliases not fully expanded by SHB, platform-dependent integers without a target
code, and unknown tags. A nominal declaration ID is itself SHA-256 of the domain
`simple.nominal-decl.v1` and package/module/SHB-serial components in the same
envelope. The encoder is implemented once in a common compiler metadata module;
packer and runtime transport and compare its output rather than reimplementing
normalization. Domain separation prevents cross-kind substitution.

| Type | Canonical input |
|---|---|
| `ConcreteTypeIdV1` | domain `simple.concrete-type.v1`, package-lock identity, normalized module identity, nominal declaration identity, and recursively encoded concrete generic arguments |
| `FacetInterfaceIdV1` | domain `simple.facet-interface.v1`, package-lock identity, normalized module identity, nominal facet declaration identity, and recursively encoded concrete generic arguments |
| `FacetMethodIdV1` | domain `simple.facet-method.v1`, interface ID, declaration ordinal, and normalized method name |
| `FacetImplIdV1` | domain `simple.facet-impl.v1`, implementation declaration identity, concrete-type ID, and interface ID |
| `FacetBindingIdV1` | domain `simple.facet-binding.v1`, concrete-type ID, interface ID, implementation ID, module ID, module-content hash, and pack-content hash |

The component order and representation are exact:

- concrete/interface ID: package hash `[32]`, module identity `[32]`, nominal
  declaration ID `[32]`, type-argument count `u32-le`, then one canonical type
  component per argument;
- method ID: interface ID `[32]`, declaration ordinal `u32-le`, NFC method-name
  UTF-8;
- implementation ID: implementation declaration ID `[32]`, concrete ID `[32]`,
  interface ID `[32]`;
- binding ID: concrete ID `[32]`, interface ID `[32]`, implementation ID `[32]`,
  module identity `[32]`, module content hash `[32]`, pack content hash `[32]`.

`ModuleIdentityV1` is SHA-256 of domain `simple.module.v1`, package hash, and
normalized logical module path. Content hashes are raw SHA-256 bytes. Each item
above is one envelope component; the recursive type component already carries
its own deterministic lengths. No optional field is omitted: absent optional
data is a zero-length component in contracts that define it.

`FacetContractAbiHashV1` hashes the interface ID and the ordered, normalized
method/effect/ownership ABI records. `FacetMethodSignatureHashV1` hashes the
fully lowered ABI signature, including the hidden call context. An implementation
hash is distinct from both; equality of names is never ABI evidence.

Both hashes are opaque four-`u64` newtypes and use the same envelope.
`FacetContractAbiHashV1` uses domain `simple.facet-contract-abi.v1` with
components: interface ID, method count `u32-le`, then for each declaration-order
method its method ID, signature hash, effect bits `u64-le`, receiver-ownership
tag `u8`, and result-ownership tag `u8`. `FacetMethodSignatureHashV1` uses domain
`simple.facet-method-signature.v1` with components: NFC target triple,
calling-convention tag `u8`, pointer width `u8`, hidden
`FacetCallContextV1`-pointer tag, argument count `u32-le`, each argument's
length-prefixed canonical ABI type, result ABI type, ownership bits `u64-le`,
effect bits `u64-le`, and `NO_UNWIND=1`. Unknown effect/ownership/ABI type tags
are rejected rather than hashed.

`FacetImplAbiHashV1` is a third opaque four-`u64` SHA-256 newtype. It uses domain
`simple.facet-impl-abi.v1` with these exact ordered components: facet
implementation ID `[32]`, concrete type ID `[32]`, interface ID `[32]`,
`state_scope:u8`, `access_flags:u32-le`, required core public ABI hash `[32]`,
required layout hash `[32]` (all zero when absent), factory signature hash `[32]`,
destroy signature hash `[32]` (all zero when absent), method count `u32-le`, then
for every declaration-order method: method ID `[32]`, signature hash `[32]`,
slot `u32-le`, method flags `u32-le`, and callable symbol identity hash `[32]`.
The facet-module compiler produces it from admitted HIR/ABI metadata; the packer
copies it without recomputation into ModuleEntry V4 and Catalog V3 binding
summary, and the witness carries it in `facet_impl_abi_hash`. Loader admission
requires all three authenticated copies and its recomputation from validated
witness/callable records to match exactly.

The compiler emits the IDs and hashes into SHB contract metadata. The packer
copies the exact fixed-size values into the catalog and module witness records.
The loader compares bytes; it does not recreate IDs from runtime source names.

### Runtime concrete-type authority

The static receiver type is only an inline-cache hint. Acquisition uses a
compiler-emitted immutable `ConcreteTypeDescriptorV1` carried by the receiver's
runtime representation. It contains `ConcreteTypeIdV1`, public ABI hash, optional
layout hash, target/runtime ABI version, and an owning module handle.

Interface receivers must retain the concrete descriptor in their fat pointer.
Reference receivers also expose a stable object-identity token used to share a
lazy sidecar for `(object identity, binding ID, generation)`. A value receiver is
boxed into a rooted snapshot; it may use only public-readonly facet access.
Private inspection or mutation on a value snapshot is refused.

No implementation may infer a concrete type ID by parsing a type name or by
trusting a static generic parameter.

## Authenticated witness metadata

Ordinary SMF facet modules gain one registered `.facet_witness` section. The
wire type is proposed as byte **17**, after `.aspect_pack` byte 16; it is not
reserved until the Simple and Rust SMF enum registries are changed together.
Exactly one section is permitted in a facet module. Ordinary non-facet modules
may omit it. A facet route to a module with zero or multiple sections is refused.

All integers are little-endian. Offsets are from the start of the section and
must be aligned, in bounds, non-overlapping, and representable without overflow.
Reserved fields and unknown flags must be zero.

### `FacetWitnessHeaderV1` — 96 bytes

| Offset | Field | Value |
|---:|---|---|
| 0 | `magic[8]` | ASCII `SMFFWIT1` |
| 8 | `version:u16` | `1` |
| 10 | `header_size:u16` | `96` |
| 12 | `flags:u32` | `0` |
| 16 | `binding_count:u32` | nonzero |
| 20 | `method_count:u32` | sum of binding method counts |
| 24 | `callable_count:u32` | exact referenced callable count |
| 28 | `reserved0:u32` | `0` |
| 32 | `bindings_offset:u64` | 8-byte aligned |
| 40 | `methods_offset:u64` | 8-byte aligned |
| 48 | `callables_offset:u64` | 8-byte aligned |
| 56 | `bindings_size:u64` | `binding_count * 320` |
| 64 | `methods_size:u64` | `method_count * 80` |
| 72 | `callables_size:u64` | `callable_count * 80` |
| 80 | `section_size:u64` | exact section length |
| 88 | `reserved1:u64` | `0` |

### `FacetWitnessBindingV1` — 320 bytes

The first 224 bytes are seven 32-byte values in this order:

1. `concrete_type_id`
2. `facet_interface_id`
3. `facet_impl_id`
4. `facet_contract_abi_hash`
5. `facet_impl_abi_hash`
6. `required_core_public_abi_hash`
7. `required_core_layout_hash` (all zero for public-only access)

The final 96 bytes are:

| Relative offset | Field |
|---:|---|
| 224 | `first_method:u32` |
| 228 | `method_count:u32` |
| 232 | `factory_callable_index:u32` |
| 236 | `destroy_callable_index:u32` (`0xffffffff` means none) |
| 240 | `witness_abi_version:u32` (must be 1) |
| 244 | `state_scope:u8` |
| 245 | `binding_flags:u8` (must be 0 in V1) |
| 246 | `reserved0:u16` (must be 0) |
| 248 | `factory_signature_hash[32]` |
| 280 | `destroy_signature_hash[32]` (all zero when absent) |
| 312 | `access_flags:u32` |
| 316 | `reserved1:u32` (must be 0) |

Allowed access flags are `PUBLIC_READONLY=1`, `PRIVATE_INSPECT=2`,
`MUTATE=4`, and `STRUCTURAL_UNSAFE=8`. The selected policy and layout hashes
must authorize every set bit; unknown bits refuse admission.

`FacetStateScopeV1` is the closed wire-`u8` enum `STATELESS=0`,
`PER_BINDING=1`, or `PER_OBJECT=2`; every other value is refused. Stateless output has no sidecar.
Per-binding state is created once before binding publication with zero
base/object handles and is shared by every reference. Per-object state is keyed
by exact object identity, binding ID, and committed generation.

### `FacetWitnessMethodV1` — 80 bytes

| Relative offset | Field |
|---:|---|
| 0 | `method_id[32]` |
| 32 | `signature_hash[32]` |
| 64 | `callable_index:u32` |
| 68 | `slot:u32` |
| 72 | `flags:u32` (must equal `NO_UNWIND=1` in V1) |
| 76 | `reserved:u32` |

### `FacetCallableAbiV1` — 80 bytes

| Relative offset | Field |
|---:|---|
| 0 | `symbol_index:u32` |
| 4 | `kind:u8` (`FACTORY=1`, `DESTROY=2`, `METHOD=3`) |
| 5 | `calling_convention:u8` (`TARGET_C=1`) |
| 6 | `pointer_width:u8` (`4` or `8`) |
| 7 | `flags:u8` (must equal `NO_UNWIND=1`) |
| 8 | `signature_hash[32]` |
| 40 | `symbol_identity_hash[32]` |
| 72 | `reserved:u64` (must be 0) |

Each referenced factory, destroy thunk, and method points to exactly one
callable record of the required kind. No callable index or symbol index may be
duplicated. `symbol_identity_hash` is SHA-256 over domain
`simple.smf-callable.v1`, normalized symbol identity, kind, binding/visibility,
target ABI, and signature hash using `FacetIdentityEncodingV1`. The compiler
emits this callable ABI table alongside code; the selected module content hash
and pack trust proof authenticate it. The loader recomputes the symbol identity
from the parsed SMF symbol record, compares both hashes and all ABI fields, and
only then converts the sealed symbol address to a callable pointer. Machine code
is never introspected to guess a signature.

Every method record's `signature_hash` must equal its referenced callable
record's `signature_hash`, just as factory/destroy hashes must equal theirs.

Slots are dense from zero and follow the facet interface declaration order.
The record range must equal the compiler contract exactly: no missing, duplicate,
extra, reordered, or unknown method is accepted. Each callable must name a
defined symbol in the same staged module and carry the expected lowered
signature. Generic facet contracts are validated after concrete instantiation;
an ABI-inexpressible method is a compile-time error, not a runtime guess.

### Authentication chain

The typed catalog schema must carry fixed-size route IDs, expected pack content
hash, expected module content hash, facet contract ABI hash, activation policy,
and signature policy. The current `ApkCatalogEntryV2` and module directory do
not carry this complete chain, so a typed Catalog V3/ModuleEntry V4 is a hard
prerequisite.

Before accepting a facet catalog, application load creates an
`ApplicationCatalogAdmissionProofV1`. Its root is either (a) an application-SMF
signature verified against an independently configured trust store, with the
catalog section inside the canonical signed region, or (b) an independently
pinned application/catalog content hash when the loader's minimum policy
explicitly permits integrity-only development mode. A loose catalog supplied by
the catalog itself cannot establish this proof.

The loader is constructed with immutable `FacetMinimumTrustPolicyV1`: minimum
trust level, allowed trust-root identities, whether integrity-only application
or pack admission is allowed, and permitted target/runtime ABI versions. Catalog
fields may strengthen these requirements but cannot weaken them. Effective
policy is the strict intersection of loader minimum, authenticated application
policy, and route policy. Trust roots never come from the catalog or pack being
checked, and catalog replacement cannot replace the minimum policy.

`FacetAdmissionProofV1` retains:

- the immutable validated catalog snapshot digest/generation and its
  `ApplicationCatalogAdmissionProofV1`;
- route record digest and typed IDs;
- pack content hash and exact signature-policy verdict;
- selected module content hash, module ABI hash, and core ABI/layout hashes;
- target triple and variant fingerprint.

The pack's content hash covers the exact pack bytes. The signature covers the
pack format's canonical signed region (all authenticated content, excluding the
signature value itself). When policy requires a signature, Ed25519 verification
against the independently configured trust root must pass. An
unsigned-but-policy-permitted pack is explicitly marked
`integrity_only`; it is never reported as signature-authenticated. Because the
witness section lies inside the content-hashed selected module and the module is
inside the content-hashed pack, descriptor bytes are bound to the proof.

CRC32 is corruption detection only and cannot satisfy this contract.

## Witness factory and call ABI

The compiler generates factory/destroy thunks and method thunks in Pure Simple.
Their externally visible ABI is fixed-layout and versioned; the loader validates
the symbol signature before calling it. Dynamic code never supplies a vtable
pointer. The loader constructs the vtable from validated symbols.

```text
facet_witness_factory_v1(
    request: *const FacetFactoryRequestV1,
    output: *mut FacetFactoryOutputV1
) -> i32

facet_witness_destroy_v1(
    request: *const FacetDestroyRequestV1
) -> i32

facet_method_slot_N(
    context: *const FacetCallContextV1,
    <normalized user arguments>
) -> <normalized user result>
```

`FacetFactoryRequestV1` contains ABI version/size, rooted base handle, concrete
descriptor handle, staged binding handle, staging token, capability-context
handle, and allocator handle. It deliberately does not expose a generation:
generations are assigned only by successful publication. `FacetFactoryOutputV1`
contains ABI version/size, flags,
and one opaque sidecar handle. All output bytes are zero-initialized by the
loader before the call. Nonzero return, changed version/size, unknown flags, or
an invalid sidecar handle fails the transaction.

V1 uses the target C calling convention, little-endian fixed-width fields, and
8-byte structure alignment. Its opaque handles are `u64` on every target; an
unsupported target ABI is refused before mapping. Pointer parameters themselves
use the target pointer width. The layouts are exact:

### `FacetFactoryRequestV1` — 64 bytes

| Offset | Field |
|---:|---|
| 0 | `abi_version:u32` (= 1) |
| 4 | `struct_size:u32` (= 64) |
| 8 | `base_root_handle:u64` |
| 16 | `object_identity_handle:u64` |
| 24 | `concrete_descriptor_handle:u64` |
| 32 | `binding_handle:u64` |
| 40 | `staging_token_handle:u64` |
| 48 | `capability_context_handle:u64` |
| 56 | `allocator_handle:u64` |

### `FacetFactoryOutputV1` — 32 bytes

| Offset | Field |
|---:|---|
| 0 | `abi_version:u32` (= 1) |
| 4 | `struct_size:u32` (= 32) |
| 8 | `flags:u64` (`SIDECAR_PRESENT=1`; every other bit invalid) |
| 16 | `sidecar_handle:u64` (zero for stateless) |
| 24 | `reserved:u64` (= 0) |

### `FacetDestroyRequestV1` — 72 bytes

| Offset | Field |
|---:|---|
| 0 | `abi_version:u32` (= 1) |
| 4 | `struct_size:u32` (= 72) |
| 8 | `base_root_handle:u64` |
| 16 | `object_identity_handle:u64` |
| 24 | `binding_handle:u64` |
| 32 | `generation:u64` (zero for pre-publication rollback) |
| 40 | `staging_token_handle:u64` |
| 48 | `sidecar_handle:u64` |
| 56 | `capability_context_handle:u64` |
| 64 | `allocator_handle:u64` |

### `FacetCallContextV1` — 56 bytes

| Offset | Field |
|---:|---|
| 0 | `abi_version:u32` (= 1) |
| 4 | `struct_size:u32` (= 56) |
| 8 | `base_root_handle:u64` |
| 16 | `object_identity_handle:u64` |
| 24 | `sidecar_handle:u64` |
| 32 | `binding_handle:u64` |
| 40 | `generation:u64` |
| 48 | `capability_context_handle:u64` |

Factory/destroy status `0` means success; every nonzero value is failure. The
loader maps implementation-private statuses to `E-AFW-004` without exposing
untrusted text. The normalized signature hash includes calling convention,
target triple, pointer width, hidden context, user parameters/result, ownership,
effects, and unwind policy. V1 thunks are non-unwinding; an unwind across the
boundary quarantines the staged or live generation.

The loader derives the expected factory and destroy signature hashes itself from
the fixed prototypes and layouts above through the canonical ABI type encoder;
it never accepts a hash merely because the module repeats it in two fields.
Binding hash, callable hash, loader-derived hash, pointer width, and target must
all agree before an address is invoked.

`SIDECAR_PRESENT` is clear exactly when `sidecar_handle` is zero and set exactly
when it is nonzero. It is clear for `STATELESS` and set for `PER_BINDING` and
`PER_OBJECT`. Factory/destroy hashes in the binding record must equal their
referenced authenticated `FacetCallableAbiV1` hashes. Destroy index and hash are
both absent for stateless state and both present for stateful scopes.

`FacetDestroyRequestV1` carries the same staged/binding/base authority plus the
sidecar handle. A rollback uses generation zero and the single-use staging token;
a live destroy uses the committed generation. A stateless generated factory
returns sidecar zero and needs no destroy symbol. Stateful sidecars are
reference-owned by an immutable
`FacetInstanceControlV1`; the instance table is keyed by stable object identity,
binding ID, and generation.

`FacetCallContextV1` carries only rooted base, sidecar, immutable binding handle,
exact generation, and capability-context handle. A thunk revalidates liveness
before entering implementation code. Raw addresses and these internal handles
are not available to user source.

### Loader-owned vtable

After method validation the loader builds an immutable table:

```text
FacetVTableV1 header (96 bytes, 8-byte aligned):
  0  abi_version:u32 = 1
  4  header_size:u32 = 96
  8  slot_count:u32
 12  pointer_width:u8 = 4 or 8
 13  endianness:u8 = 1 (little)
 14  flags:u16 = 0
 16  interface_id[32]
 48  contract_abi_hash[32]
 80  owner_mapping_handle:u64
 88  slots_offset:u64 = 96

At offset 96: `slot_count` target-native `uintptr` values, each aligned to the
pointer width. Total size is `96 + slot_count * pointer_width`; overflow or
trailing storage is refused.
```

Every slot uses target-native little-endian representation and must fall within
a sealed executable segment owned by the
staged module. The table becomes read-only before publication. Facet method
lowering uses its compile-time slot and MIR `CallIndirectAbi`; it never invokes
`rt_vtable_lookup` and never resolves a method name on a hot call.

## Transactional activation

### Aspect-pack immutable admission lease

The typed path needs a non-publishing lease beside the existing compatibility
APIs:

```text
apk_prepare_typed_facet_v1(loader, typed_route, catalog_snapshot)
    -> Result<ApkTypedFacetAdmissionLeaseV1, FacetLoadError>
apk_release_typed_facet_lease_v1(lease) -> ()
```

Prepare validates the indexed route, policy, dependency closure, exact pack and
module hashes, and returns the selected immutable ordinary-SMF payload plus its
admission proof. The reference-owned lease retains the catalog/pack snapshot and
is owner-bound and catalog-generation-bound. It creates no aspect-pack binding,
mutates no aspect-pack registry, and advances no generation.

There is no second typed commit. Before publication the transaction exclusively
owns the lease. Atomic installation of the one `CommittedFacetBindingV1` record
moves that same lease reference into the record; abort/failure releases it.
Unload releases it after unmapping. Publication therefore has one mutable owner
and one dictionary install, not two registries requiring cross-owner rollback.
The existing aspect-pack binding registry remains compatibility-only and never
represents typed visibility.

V1 facet module symbols remain inside the immutable binding record's private
symbol namespace; they are never inserted into the compatibility
`global_symbols` or `modules` dictionaries. Dependency relocations resolve
against a frozen committed dependency snapshot, while the staged closure resolves
against its own private namespaces. Cross-binding symbol export is unsupported
in V1. Therefore typed publication really is one tuple-registry insertion whose
value already owns every mapping, namespace, witness, instance, proof, and lease.

The concrete publication primitive is a reference-owned
`TypedFacetRegistryOwnerV1` with one atomic/current snapshot reference:

```text
TypedFacetRegistrySnapshotV1 {
    next_generation: u64
    bindings: persistent Dict<(ConcreteTypeIdV1, FacetInterfaceIdV1),
                              CommittedFacetBindingV1>
}
```

All allocation and persistent-dictionary insertion happen in a candidate
snapshot before publication. Under the owner lock, the loader rechecks the old
snapshot identity and policy generations, stamps the candidate record with
`old.next_generation`, sets candidate `next_generation` to old plus one with
overflow refusal, then performs one non-failing snapshot-reference swap. If the
old identity changed, it discards the candidate and rebuilds or returns a stable
conflict before any visible mutation. The current value-semantic `ModuleLoader`
fields are not mutated piecemeal and cannot serve as this owner.

### `ModuleLoadTransactionV1`

For one `(ConcreteTypeIdV1, FacetInterfaceIdV1)` acquisition:

1. Read the receiver's authenticated concrete descriptor; validate the facet
   contract, capability, critical mode, loader seal, and typed IDs.
2. Check the committed tuple registry. A live hit pins and returns without I/O.
3. Join or create one single-flight activation for the tuple and target catalog
   generation. The current single-owner behavior is not evidence of concurrency.
4. Ask aspect-pack prepare for an admission lease and immutable SMF payload.
5. Parse the in-memory ordinary SMF once. Require exactly one valid witness
   section and select exactly one matching binding record.
6. Validate proof, target, runtime ABI, public/layout hashes, method set,
   signature hashes, symbol indices, access grants, and dependency closure.
7. Begin a staged SegmentMapper owner. Allocate/map all needed segments without
   inserting global symbols or committed module rows.
8. Resolve relocations against an immutable committed-symbol snapshot plus the
   transaction's own staged symbols. Apply relocations while writable.
9. Seal segments to their final permissions, flush instruction caches, resolve
   factory/method/destroy addresses, prove every address belongs to the sealed
   staged owner, and build/seal the loader-owned vtable.
10. For `STATELESS`, invoke the factory with zero receiver handles and require
    zero sidecar. For `PER_BINDING`, invoke it once with zero receiver handles
    and stage the shared sidecar. For `PER_OBJECT`, invoke it for the requesting
    receiver and stage that object's instance control. No global acquisition can
    observe a result.
11. Build the candidate persistent registry snapshot. Under the loader
    publication lock, recheck prior snapshot identity, catalog generation, seal
    state, absence of a conflicting binding, and dependency generations. Stamp
    the candidate with the next never-reused generation and perform the one
    no-fail snapshot-reference swap, installing one immutable committed
    record containing module namespace, mappings, witness, instance, proof,
    immutable admission lease, and state `BOUND`.
12. Create and pin the public `FacetRef<T>` control only after commit, complete
    the single-flight, and wake waiters with the same committed generation.

If any step fails, the loader destroys a staged sidecar if factory execution had
begun, discards the vtable, removes staged symbols, unmaps every staged segment,
releases the admission lease, and completes the single-flight with one stable
error. No binding or generation is advanced. Cleanup failure quarantines the
owner and keeps its memory inaccessible/non-reusable; it still does not publish.

The transaction must be implemented as one reference-owned mutable capsule or
one authoritative `me` mutation path. Copying value-semantics loader structs
between helpers is not an atomicity mechanism.

## Resident acquisition and caching

The committed registry key is the fixed tuple `(ConcreteTypeIdV1,
FacetInterfaceIdV1)`. Hash collisions are resolved by comparing both complete
IDs. Its value contains the current immutable binding record and generation.

- `try_facet<T>` uses only the receiver descriptor, execution-context loader,
  committed tuple registry, instance table, and pin operation. Stateless and
  per-binding state pins immediately. Per-object state joins/creates an
  object-instance single-flight and may invoke only the already-resident no-I/O
  factory; factory failure returns `None` and records a stable loader diagnostic.
  A route/binding miss is `None`.
- `facet<T>` may execute the transaction when policy permits. A route miss is
  `Ok(None)`; an admission failure is `Err`.
- `require_facet<T>` is the same load policy but converts a route miss to the
  stable required-facet error.

The execution-context loader is an explicit hidden capability threaded through
compiled entry points and interpreter `EvalContext`; there is no process-global
ambient loader. Lazy operations carry a dynload/I/O effect and are rejected
after critical sealing. Resident `try_facet` remains legal after seal.

An optional per-call-site cache stores concrete descriptor handle, interface ID,
catalog generation, binding handle, and binding generation. Any mismatch falls
back to the tuple registry. Catalog replacement, module unload, or binding
quiescence invalidates it by generation; no cache invalidation scans call sites.

For a second object under `PER_OBJECT`, acquisition runs a binding-resident mini
transaction keyed by `(object identity, binding ID, generation)`: single-flight,
acquire an internal exact-generation activation guard while state is `BOUND`,
invoke the authenticated factory, stage the instance control, recheck the
binding is still `BOUND`, then insert exactly once. Failure destroys staged state
and releases the guard without taking a public pin. On success while still
`BOUND`, instance insertion and public-pin acquisition happen under the binding
lock before the activation guard is released. If state became `QUIESCING`, the
sidecar is destroyed under the guard and acquisition fails. The factory contract is statically limited to allocator and
capability calls and cannot perform I/O, dynload, catalog access, or mapping.
Concurrent duplicate results are destroyed before returning the one committed
instance. `facet`/`require_facet` report a factory error; `try_facet` has no error
channel and therefore fails closed to `None`.

## `FacetRef<T>` and unload

`FacetRef<T>` is an opaque reference-semantics value whose shared control block
contains rooted base reference, concrete/interface/binding IDs, loader handle,
immutable vtable handle, sidecar instance handle, exact generation, and active
state. Copies share the control block. The first construction takes one binding
pin; final control-block destruction releases it. Release is idempotent.

Each binding control separately counts public generation pins, activation
guards, and invocation guards. An activation guard is granted only while
`BOUND`; quiescing blocks new factories. An invocation guard is granted in
`BOUND` or `QUIESCING` only when presented with an already-live public pin, so a
call that races final reference release still keeps code mapped. Facet invocation
acquires the exact-generation guard before reading the vtable and releases it
after return/unwind cleanup. Guards are internal, non-copyable, and owner-bound.

`FacetExecutionGuardV1` contains private loader-owner handle, binding ID,
generation, kind (`ACTIVATION=1` or `INVOCATION=2`), and active bit. Construction
and idempotent release are loader-only. A guard validates all identity fields
against the binding control before increment/decrement, so a stale guard cannot
affect a reloaded generation.

Unload is ordered:

1. Atomically change `BOUND` to `QUIESCING` and remove the tuple from new
   acquisition. Existing references remain callable.
2. Refuse new public pins and activation guards. Wait for the exact generation's
   public-pin, activation-guard, and invocation-guard counts to all reach zero.
3. Run every remaining sidecar destroy thunk while code is still mapped. Remove
   instance-table entries and roots.
4. Remove witness/vtable and module symbol visibility.
5. Unmap the generation's mappings and release dependencies.
6. Release the immutable aspect-pack admission lease and mark `UNLOADED`.

If destroy or unmap fails, state becomes `QUARANTINED`; the mapping and generation
are retained and never reused. The loader never reports `UNLOADED` while code or
sidecars remain. Catalog invalidation and loader destruction must refuse while
pins or quarantined cleanup remain, unless an explicit process-termination policy
owns the leak.

## Frontend and lowering boundary

The source grammar reserves only these generic member-call forms:

```text
postfix_expr . try_facet < type > ( )
postfix_expr . facet < type > ( )
postfix_expr . require_facet < type > ( )
```

Ordinary `obj.facet()` and ordinary comparison syntax are unchanged. A
speculative parse commits to the reserved form only after it recognizes a type
argument followed by the call delimiter; once committed, missing `>`, multiple
types, or value arguments receives a facet-specific diagnostic.

The canonical AST appends `FacetAcquire(receiver, interface_type, mode)` and a
three-case `FacetAcquireMode`; it does not add type arguments to every existing
`MethodCall` and does not encode a type as a value-expression marker. The flat
AST gets the corresponding tag and typed child slot, and the bridge preserves it.

HIR appends:

```text
HirFacetAcquireMode { TryResident, LoadOptional, LoadRequired }
HirFacetInterfaceRef {
    symbol: SymbolId,
    instance_type: HirType,
    interface_id: FacetInterfaceIdV1,
    contract_abi_hash: FacetContractAbiHashV1
}
HirExprKind.FacetAcquire(
    receiver: HirExpr,
    interface: HirFacetInterfaceRef,
    mode: HirFacetAcquireMode
)

FacetMethodResolutionV1 {
    interface_symbol: SymbolId,
    method_symbol: SymbolId,
    interface_id: FacetInterfaceIdV1,
    contract_abi_hash: FacetContractAbiHashV1,
    method_id: FacetMethodIdV1,
    signature_hash: FacetMethodSignatureHashV1,
    slot: u32
}
MethodResolution.FacetMethod(FacetMethodResolutionV1)
```

The type checker requires exactly one resolved sealed facet-interface instance,
validates access/effects, and assigns exact types:

- `TryResident` -> `Option<FacetRef<T>>`
- `LoadOptional` -> `Result<Option<FacetRef<T>>, FacetLoadError>`
- `LoadRequired` -> `Result<FacetRef<T>, FacetLoadError>`

Unknown types, ordinary traits/classes, open/unsealed contracts, unsupported ABI
methods, and unauthorised effects are errors. No fresh unconstrained result type
is permitted.

The ordinary HIR `MethodCall` remains the call carrier, but resolution on a
`FacetRef<T>` must produce `MethodResolution.FacetMethod`; it may never remain
`Unresolved`, degrade to name/trait lookup, or discard the slot/IDs/hashes.

MIR lowering emits a typed facet-acquisition operation carrying mode and fixed
IDs, plus a loader-context operand. The facet method resolution lowers to an
explicit checked vtable load followed by
`CallIndirectAbi` with `MirFacetCallAbiV1` and `FacetCallContextV1`. There is no unresolved `MethodCall`,
runtime type-name parsing, or runtime method scan.

## Diagnostics

The implementation reserves these stable families:

| Code | Meaning |
|---|---|
| `E-AF-TYPE-001` | missing/multiple facet type argument or value arguments |
| `E-AF-TYPE-002` | target is not a sealed facet interface |
| `E-AF-EFFECT-001` | lazy acquisition is forbidden by capability/critical policy |
| `E-AFW-001` | witness section missing, duplicate, malformed, or unsupported |
| `E-AFW-002` | concrete/interface/implementation/ABI identity mismatch |
| `E-AFW-003` | method set, slot, symbol, or signature mismatch |
| `E-AFW-004` | factory or destroy ABI/return contract failure |
| `E-AFTXN-001` | map, relocation, seal, or address-ownership failure |
| `E-AFTXN-002` | stale catalog/dependency generation or publication conflict |
| `E-AFTXN-003` | rollback cleanup quarantined the staged owner |
| `E-AFUNLOAD-001` | pinned generation cannot yet unload |
| `E-AFUNLOAD-002` | destroy/unmap failed and generation is quarantined |

Pack/hash/signature failures retain the existing `E-APACK` family. Diagnostics
must not expose raw addresses or trust a malformed identifier for formatting.

## Implementation prerequisites and blockers

Typed facet implementation is blocked until all of these are accepted and land:

1. a selected requirement for the Option-C typed language surface;
2. one canonical `FacetIdentityEncodingV1` implementation and opaque 32-byte ID
   types across compiler metadata, packer, HIR/MIR, and runtime;
3. authenticated application-catalog admission plus an independently configured,
   non-downgradable `FacetMinimumTrustPolicyV1`;
4. Catalog V3/ModuleEntry V4 content-hash and fixed typed-route fields;
5. synchronized `.facet_witness`/callable ABI reader/writer support with the
   exact state-scope and callable layouts;
6. compiler-emitted facet contracts and concrete runtime descriptors;
7. rollback-safe staged SegmentMapper and single-owner immutable admission-lease
   transfer into atomic ModuleLoader publication;
8. explicit loader capability in compiled and interpreter execution contexts;
9. binding and per-object single-flight with a real concurrency primitive and
   exact factory rollback;
10. `MethodResolution.FacetMethod` schema/codec/visitor/resolution transport
    through MIR `FacetInvoke` without losing slot or hashes;
11. exact `MirFacetCallAbiV1`, facet-op elimination/absence verification, and
    explicit `CallIndirectAbi` handling or rejection in every optimizer/backend;
12. HIR interpreter facet-method dispatch through the explicit loader/vtable
    path or a pre-evaluation unsupported diagnostic;
13. native x86_64 `CallIndirectAbi` lowering (or an explicit unsupported-target
    diagnostic before source admission);
14. exact sidecar identity/rooting plus activation/invocation guard counters and
    unload cleanup ownership.

Until then, pending acceptance specs stay pending and the source forms are not
claimed as implemented.

## Consequences

- The design adds metadata and a transaction, but removes runtime name parsing,
  symbol scans, repeated catalog decoding, and unsafe bytes-to-type shortcuts.
- The witness table is loader-owned and immutable, so the module cannot swap a
  method after validation.
- Dynamic facets do not change the base object's nominal layout. Private/layout
  access remains an explicit, hash-bound capability.
- The compatibility text/payload API remains useful for pack tooling and tests,
  but typed code cannot call through it.
- Most orchestration and metadata validation can remain Pure Simple. OS mapping,
  page protection, instruction-cache flush, and raw indirect call remain narrow
  runtime/backend boundaries.

## References

- `doc/03_plan/compiler/aspect_dynload/aspect_dynload_lane_plan_2026-08-19.md`
- `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`
- `doc/04_architecture/compiler/aspect_dynload/blocking_infrastructure_interfaces_2026-08-19.md`
- `src/lib/common/aspect_pack.spl`
- `src/compiler/99.loader/module_loader_compat.spl`
- `src/compiler/99.loader/segment_mapper.spl`
- `src/compiler/50.mir/mir_instruction_kinds.spl`
- `src/compiler/70.backend/backend/native/isel_x86_64.spl`
