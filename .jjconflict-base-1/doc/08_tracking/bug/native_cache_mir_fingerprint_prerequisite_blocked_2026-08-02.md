# Native-cache MIR fingerprint prerequisite is not yet representable

- **ID:** `native_cache_mir_fingerprint_prerequisite_blocked_2026-08-02`
- **Status:** BLOCKED — claimed and audited by `pure_parser_close` on 2026-08-02
- **Severity:** High (cache correctness prerequisite)

## Finding

The existing `serialize_mir_module` cannot safely seed cache metadata. It emits
only module name and functions, iterates `module.functions.values()` without a
canonical key order, and omits `statics`, `constants`, and `types`. Two modules
that generate different objects can therefore serialize identically, while one
module can serialize differently across dictionary iteration orders.

The native-object cache call site also writes `dependencies: []`. The available
SMF helper collects hashes only for top-level input paths, not each MIR module's
ordered direct imports, so copying it would falsely label incomplete dependency
data as authoritative.

## Safe implementation boundary

Before metadata can be added, implement a canonical MIR serializer that sorts
symbol keys and covers functions, statics, constants, types, signatures,
locals, blocks, instructions, terminators, and referenced symbol identities.
Separately derive direct imports per module and resolve each to its SHB interface
hash, sorting `(canonical module path, interface hash)` rows before hashing.

Only then persist optional `mir_fingerprint` and `dependency_interfaces` fields;
old cache files must default both to absent and global cache admission must remain
unchanged until parity tests prove the new keys complete.

## Measurement

Serialization overhead cannot be honestly measured until the complete serializer
exists. The current incomplete serializer is rejected as a benchmark target.
Cache-hit delta remains zero and correctness is unchanged.

