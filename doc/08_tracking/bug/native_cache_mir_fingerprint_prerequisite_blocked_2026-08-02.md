# Native-cache MIR fingerprint prerequisite is not yet representable

- **ID:** `native_cache_mir_fingerprint_prerequisite_blocked_2026-08-02`
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
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


## Verification 2026-08-17 (w02/s4 lane) — CONFIRMED LIVE / still BLOCKED

Classified by CONTENT (session brief CORRECTION 1).

`grep -rn 'interface_digest_of' src/` returns four lines, and **none of them is a
call**:

- `src/compiler/80.driver/cache/action_key.spl:199` — the definition itself,
  `fn interface_digest_of(parts: [text]) -> text`
- `src/compiler/35.semantics/interface/compile_interface.spl:37` — a comment
- `src/compiler/80.driver/cache/block/block_key.spl:10` — a comment
- `src/compiler/80.driver/cache/schema/cache_protocol.sdn:844` — a schema entry

This independently reproduces the census recorded in `.claude/rules/commands.md`
("grep -rn interface_digest_of src returns one line: its own definition. Zero
callers — never computed, not merely ignored"), now re-measured against current
source rather than inherited from the doc. The function is computed by nobody, so
no interface-digest edge exists and native-cache correctness still cannot be
validated.

**Verdict: LIVE, still BLOCKED as the doc states. No patch applied** — this is a
missing dependency/target model (`simple.sdn` traversal + `SmfManifest`
load-verification), not a defect with a local fix.
