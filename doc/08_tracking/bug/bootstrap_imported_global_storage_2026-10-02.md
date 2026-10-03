# Imported globals lose declaration type and provider storage

Status: implementation candidate; native and unit execution UNRUN.

The retained Linux two-module discriminator imports a provider's public
`[text]` literal and iterates it. On producer
`184d1be492926713d19bfb95ba2705cb31a2fb6affe8ebea9e1874185d6ef921`,
MIR reports the imported name undefined, then reports an unsupported I64
iterable. Evidence is retained in the producer checkout's
`build/atomic-receiver-discriminator-20261002/imported-array-relative.log`.
This matches catalog F0002/F0005 (ANY_CLASSES); it does not establish that
every method-resolution or iterable diagnostic has the same cause.

HIR import registration previously discarded the constant's declared type and
used a local alias as the declaration name. MIR global lookup only indexed the
current module's constants/statics. The candidate preserves declaration owner,
source name, type and mutability, then binds demanded imported IDs to external
provider storage. It never copies provider initializer expressions into the
consumer. Non-private provider constants retain a linkable owning slot.

Provider initialization uses guarded owner entries. Imported data accesses,
direct imported calls and imported callable values enter the provider first.
The guard detects active dependency cycles and skips completed initialization.
Ordinary and flat bootstrap lowering share this registration. Flat static
external flags participate in existing transient promotion and reset paths.

Regression cases cover literal arrays, initialized arrays, mutable storage
shared by readers and writers, same-name aliased providers, scoped visibility,
direct and function-mediated initializer dependencies, and cycles. See
`doc/05_design/imported_global_binding_2026-10-02.md` for the bounded contract
and explicit backend/type limitations.

Integration requires separate duplicate-static compaction commit `829d89e72a`
(PR #2175). Nominal global receiver identity is separately repaired by
`2bbeac34c3` (PR #2172); this change does not duplicate that hunk.
No production-ready or cross-host execution claim is made from static checks.
