<!-- codex-design -->
# Architecture: SFFI v2 Hardening

**Status:** P0/P1 normative; P2–P6 planned  
**Requirements:** `doc/02_requirements/feature/sffi_v2_hardening.md`

## Decision

SFFI v2 is one compiler-owned contract capsule with generated lane adapters:

```text
foreign implementation
 -> versioned C ABI shim
 -> raw binding / ForeignRaw<T>      [unsafe(ffi)]
 -> contract validator and lift
 -> safe T | Option<T> | Result<T,SffiError>
```

The contract, not a symbol-name table or handwritten wrapper, is authoritative.
Each engine may have a physical thunk, but no engine may reinterpret the
contract or invent a fallback provider.

## Virtual capsules and transforms

`SffiContractCapsuleV2` owns canonical types, return families, ownership,
allocator, unwind/thread/callback policy, diagnostics, and hashes. It exposes
read-only resolved contracts to:

- frontend/HIR safety;
- interpreter thunk generation;
- JIT/native lowering and closure resolution;
- dynloader/provider admission;
- C/C++/Rust/Simple wrapper generation;
- test/doc generation.

Cross-cutting validation is a feature transform from `SffiRaw(contract_id)` to
`SffiLifted(wrapper_id, contract_id)`. The transform inserts status/null/
sentinel/descriptor checks once at the boundary and prevents `ForeignRaw<T>`
from escaping. It is not aspect advice that can be dropped after weaving.

## P0 return and failure model

Execution produces `(ReturnOrigin, Option<Value>)`, where origin distinguishes
explicit return, tail expression, unit fallthrough, explicit optional none,
foreign return, foreign error, and missing return. A total validator maps this
pair and the declared type to either one admitted value or `SffiError`.

Extern resolution is whole-closure and fail-closed. Missing symbols, null
function pointers, unsupported conversion, and fabricated linker definitions
are errors. Legitimate empty/zero values remain possible only when the declared
contract admits them.

## P1 contract model

`SffiFunctionContractV2` contains provider/symbol/version, ABI/calling
convention, target, parameter contracts, one return family, ownership and
allocator domains, bounds/encoding relations, unwind/thread/callback policy,
assurance requirement, contract ID, and ABI hash.

The raw ABI initially admits fixed-width scalars, target-sized values with
target identity, explicit C layouts, opaque pointers/handles, versioned spans,
status codes, and typed function pointers. Rich Simple, Rust, or C++ runtime
objects are wrapper-level only.

## Provider lifecycle (planned P3/P4)

```text
discovered -> exact artifact hashed -> signature/provenance accepted
 -> target and registry matched -> receipts accepted -> all symbols resolved
 -> immutable typed slots atomically published -> active
```

Any failure rejects the provider before partial publication. P4 signing and
evidence are planned; fields in the P1 contract must be extensible without
pretending admission already exists.

## Hot path and invalidation

Static and sealed-complete providers call direct or immutable typed slots,
followed by required status/null/sentinel/descriptor checks and lift. Admission
is invalidated by artifact, provider generation, target, profile, registry, or
contract identity change. No hot call performs lookup, hashing, signature work,
or generic marshalling.

## Error containment

C++ exceptions are caught by C shims. Rust exports use C-compatible layout and
declared panic policy. Unknown ownership is unsafe-only. If lifetime, aliasing,
bounds, or memory safety cannot be established in process, the provider is
unsafe or isolated; a signature cannot promote it to safe.

## Compatibility

Legacy declarations may be inventoried during migration but never retain
fabricated values. P0 changes are intentionally fail-closed. Safe public APIs
expose only generated/reviewed wrappers. Pure-Simple counterparts remain
preferred and foreign ownership remains in canonical no-GC sync owners.

