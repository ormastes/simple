<!-- codex-architecture -->
# MC/DC and HAL Runtime Hardening Architecture

## Status

Accepted for implementation from selected requirements B/M2/P2/E1/R3/NFR-C.

## Architectural decision

The feature is one compiler-resolved virtual capsule with two coordinated transforms:

1. an MC/DC feature transform that owns the static manifest, exact short-circuit observations, proof analysis, and three coverage policies; and
2. an `rt(hal)` contract transform that emits a stable operation manifest consumed by isolated provider and environment-executor adapters.

Static-off is resolved before instrumentation and link-closure construction. Static-on emits direct fixed-buffer probes. Dynamic mode alone emits bounded data-cell patchpoints and uses the canonical aspect-pack loader. Runtime selection never uses a per-event environment read, catalog scan, symbol lookup, allocation, or formatted log.

## Layer ownership

| Layer | Ownership |
|---|---|
| `src/compiler/00.common/` | Closed MC/DC policy, identity, manifest, witness, capacity, and error contracts |
| `src/compiler/20.hir/` | Eligible decision discovery; canonical Boolean DAG; stable semantic IDs; `rt(hal)` operation manifest |
| `src/compiler/35.semantics/` | Attribute validation, assurance propagation, capability/noalloc reachability, migration diagnostics |
| `src/compiler/50.mir/` | Exact `Begin/Condition/Commit` insertion after Boolean CFG construction and before optimization |
| `src/compiler/60.mir_opt/` | Observable-effect preservation and explicit compiler exclusions for eliminated conditions |
| `src/compiler/70.backend/` | One backend-neutral lowering contract consumed by LLVM/C/native/JIT/WASM and interpreter sink parity |
| `src/compiler/80.driver/` | Policy resolution, cache identity, closure freeze, normal+coverage gate, R3 migration milestone |
| `src/compiler/85.mdsoc/feature/mcdc/` | Virtual-capsule composition only; no runtime hot-path state |
| `src/compiler/99.loader/` | Canonical aspect catalog, pack validation, slot binding, generation publication, invalidation |
| `src/lib/common/structural/` | Frozen HAL/provider, environment-instruction, exclusion, wire, comparison, and receipt schemas |
| `src/lib/nogc_async_mut_noalloc/` | Critical fixed-capacity MC/DC sink, HAL parent, environment executor, storage and error paths |
| `src/lib/nogc_sync_mut/` | Hosted adapters and warned compatibility facades |
| test runner / counterpart evidence | Process isolation, child receipt ingress, deterministic parent comparison and commit |

Sibling layers communicate only through the common contracts. App I/O remains a compatibility forwarder and never becomes the HAL owner.

## MC/DC identity and event model

The HIR pass canonicalizes `(schema, package/module identity, enclosing symbol, authored relative path, source span, Boolean DAG)` and hashes it for a semantic decision ID. Condition IDs add canonical ordinal and atom span. Rows are sorted by semantic ID and receive dense nonzero runtime slots only after closure freeze; collision is a hard error.

The MIR sequence is:

```text
McdcBegin(decision_slot)
McdcCondition(decision_slot, ordinal, value)  # only when the atom evaluates
McdcCommit(decision_slot, final_outcome)
```

The sink stores a fixed record containing slot, epoch, sequence, evaluated mask, value mask, outcome, shard, and overflow status. Unevaluated bits encode short-circuit masking. One commit record represents one decision evaluation; there is no per-condition log or eager `[bool]` construction.

Unique-cause pairs are preferred. Masking fallback evaluates the frozen Boolean DAG under the two partial assignments and proves every changed/masked non-target condition outcome-invariant. Unknown or over-budget proof is uncovered. Empty eligible denominator fails.

## Coverage policies

- `StaticOff`: no manifest embedding, probe MIR, runtime object, coverage section/string/symbol/import, aspect catalog, or dynload reference.
- `StaticOn`: direct leaf/fixed-buffer sink operations; storage is supplied and sealed before critical entry.
- `Dynamic`: fixed slot IDs and one bounded indirect data-cell dispatch at eligible sites. Explicit activation validates pack, manifest, ABI, and capacity before atomically publishing a generation.

Joinpoint slots are pointer data: RW during construction, R when published, and R→RW→R for batch patching; never executable. Acquire-load/release-store plus quiescence ensures a reader observes a complete old or new generation. Failure restores the prior table. Critical activation after the initialization boundary is rejected.

The pack cache key includes canonical path, content/file identity, catalog fingerprint, ABI, and generation. Size-only freshness is forbidden. Catalog/profile changes, replacement/hash mismatch, unload, ABI change, or dependency change invalidate the affected generation and reverse dependencies.

## `rt(hal)` contract

`@rt(hal, "operation.id.v1", ...)` is an ordinary attribute interpreted by semantic analysis, not new declaration grammar. Its frozen row contains operation ID, assurance floor, provider/capability masks, comparator/normalizer IDs, side-effect policy, fixed capacities, error/environment schemas, and preferred provider.

Unqualified operations resolve to `Critical`. Lower classification needs bounded rationale and is rejected when reached from a Critical/Verified closure. Effective policy is the maximum of entry and operation floors. Critical/Verified closures use the noalloc family and caller-owned or fixed-capacity buffers after `seal()`.

Pure Simple, C, and Rust providers run in distinct preinitialized OS processes/sandboxes. Children receive immutable bounded requests and return one bounded encoded result. They inherit no writable file descriptors, ambient environment, shared mutable pointers, clocks, randomness, or devices. The parent owns invocation IDs, deadlines, buffers, validation, normalization, ordering, comparison, and the only state commit.

Arrival order is irrelevant: validated receipts sort by `(invocation_id, provider_kind)`. Alpha commits nothing on any difference; beta follows its explicit commit policy and emits a bounded critical report; normal launches only the preferred provider. No config selects a manifest-pinned safe default.

## Environment interaction

Effectful operations use Plan-Then-Commit. Providers extract typed instructions without performing effects. The parent compares plans, performs one accepted plan, records observations, and replays the same sealed trace to shadow providers. Physically non-repeatable IRQ/MMIO/DMA/clock/random activity is captured once and replayed.

The versioned opcode set covers file, stream, process, environment, clock, randomness, socket, IRQ, MMIO, and DMA interactions. Requests and observations use fixed scalars plus `(offset,length)` into caller-owned regions. Unknown versions/opcodes, invalid lengths, duplicate or reordered sequence IDs, missing/extra instructions, unsafe requests, timeout, overflow, or incomplete consumption fail closed.

## Exclusions

Only `CapabilityUnavailable`, `FixtureUnavailable`, `PlatformInapplicable`, `SafetyProhibited`, and `UncontrollableNondeterminism` are eligible. A record contains scenario/decision identity, stable code, bounded human reason, registered predicate, evidence digest, owner, review, and expiry. Validation preserves gross totals, changes only the eligible denominator, and reports `Excluded`, never PASS. Known defects remain failures.

## Memory and concurrency

Initialization may map packs, launch provider workers, and size storage. `seal()` establishes the no-allocation epoch. Every success, failure, timeout, overflow, comparison, logging, shutdown, and cleanup path after sealing uses fixed storage. Per-thread shards avoid hot-path locks; overflow sets a sticky typed failure with first-lost sequence and count.

The parent merges child receipts deterministically by manifest/binary identity, provider lane, shard, and sequence. Witness choice uses a stable lexicographic rule. No provider performs authoritative side effects and no shared-memory thread comparison qualifies as provider isolation.

## R3 migration

A pure-Simple verifier fingerprints findings by rule, canonical module, symbol, source span, and normalized signature. New/changed findings are errors immediately. Exact untouched legacy fingerprints warn until the next exact release milestone. Moved/changed findings become new errors; stale, malformed, duplicate, expired, or unowned baseline entries are errors. At the milestone every finding is an error, the baseline is empty/deleted, and compatibility shims are removed. Recording can only create a review candidate.

## Evidence and failure policy

Static-off uses normalized machine-code plus symbol/section/link-map equivalence, not timing alone. Performance receipts bind fixture, compiler, binary, manifest, raw samples, percentile method, RSS, allocation epoch, pack mappings, capacities, log bytes, overflow, and all child receipts. Any missing identity, child, raw data, allocation, evidence loss, or unsupported field fails.

External hardware rows remain explicit excluded/blocked rows with stable executor and target identity; they never become current-host PASS.

## Rejected alternatives

- Source rewriting as the production MC/DC owner: incomplete grammar/backend coverage and eager-evaluation risk.
- LLVM-only MC/DC: divergent truth models and no non-LLVM/SimpleOS completeness.
- Per-event env checks or dynamic registry lookup: violates static-off and hot-path budgets.
- Threaded providers: no fault/state isolation.
- Duplicate physical side effects per provider: unsafe and nondeterministic.
- Free-text skip or defect waiver: weakens the 100% eligible claim.
- Private MC/DC dynloader: duplicates canonical aspect-pack ownership.

