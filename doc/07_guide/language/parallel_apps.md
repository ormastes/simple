# Parallel Applications

Simple parallel code follows one default convention: the owner keeps canonical
mutable state; children read immutable input or receive explicit ownership;
children create independent results; the owner validates and commits them.

## Current contract surface

The repository now provides common vocabulary for transfer envelopes, storage
plans, access paths, parent-commit ordering, and assurance policy:

- child-created outputs are the preferred transfer direction;
- parent-owned mutable state is an explicit consuming move;
- process, remote, and device boundaries reject an ordinary owned in-memory
  region; they require an encoded/immutable handle or device lease;
- unknown dynamic ranges overlap until proven otherwise;
- external ABI/wire/MMIO storage remains pinned.

Critical policy denies implicit parent-to-child moves and dynamic transport, and
requires bounded mailboxes, deterministic commits, and frozen layout receipts.

The common commit engine now models a functional owner transition with a
constant-size final snapshot-root assignment. It first validates every result's base revision, identity, deterministic
order, and conflict policy. Only a fully valid non-empty batch advances the
revision and replaces the snapshot token. Failures return the original owner
state, and a shape-validated receipt records input/output roots plus the canonical task,
sequence, and payload-token order. The owning application adapter still builds
and verifies the candidate snapshot before supplying its token. A concurrent
runtime owner must serialize or CAS the transition against the live root; the
common value function alone is not an atomic synchronization primitive.

## Status

These are common/compiler contract foundations, not a claim that every current
actor, process, thread-pool, generic channel, or backend layout path already
enforces them. The snapshot transition does not itself interpret payloads or
run an application verifier. Runtime adapters, typed bounded public transport,
structured task groups, physical layout lowering, and end-to-end process/device
evidence remain work-package gates. Consult the receipt and the matching
runtime gate before relying on a path in production.

The native runtime currently has one deliberately narrow heap-copy building
block: boxed `f64`, boxed `u64`, and immutable UTF-8 strings can be encoded by
logical content with a bounded `EncodedCopy` packet and reconstructed with a
new heap identity. This is not a general object-graph codec. Arrays, mappings,
tuples, objects, capabilities, device values, and unauthenticated remote routes
remain rejected until their schema, ownership, or lease contract lands.

The compiler also has an initial logical storage-access analysis. Given region
identities established by ownership analysis, MIR constant-index loads and
stores retain known half-open ranges, while dynamic indices, nested indices,
unbound pointers, and field paths remain conservative. Field names are useful
layout-planning evidence but do not yet prove physical disjointness. No current
backend may infer `noalias` or claim AoS/SoA lowering from these facts alone.

The common storage contract also includes a checked reference conversion oracle
for fixed-size records. It can convert non-overlapping fields among AoS, SoA,
and tail-padded AoSoA plans and verify exact logical round trips. The oracle is
limited to 64 MiB, copies value-semantic byte arrays, and rejects malformed or
overlapping physical mappings. It is test evidence, not the optimized typed
array view or backend lowering promised by WP-22.

The MIR optimizer now also checks whether an AoSoA block is compatible with a
selected fixed-width SIMD route. Matching AVX/NEON-style widths are admitted;
AoS and SoA retain the scalar/reference fallback; ABI-pinned or mismatched
storage is rejected. SVE and RVV are recorded as explicitly deferred because
the native scalable-vector lowering path is not yet implemented. Admission is
only a legality gate: it emits no vector instructions, tail mask, or alias
metadata.

## Recommended shape

```simple
val snapshot = owner.snapshot()
val results = TaskGroup.map(parts, snapshot, build_child_result)
owner.commit(results)?
```

Do not use a raw pointer or unclassified dynamic object as a cross-domain
payload. Do not infer that two different index variables are disjoint.
