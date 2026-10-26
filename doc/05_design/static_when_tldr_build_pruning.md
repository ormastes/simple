# Static guard and closure detail design

Status: interface/design freeze for implementation planning, 2026-10-06. Not a native qualification receipt. See [architecture](../04_architecture/static_when_tldr_build_pruning.md) and [selected source](../01_research/local/simple_static_when_tldr_build_pruning_plan.md).

## Shared interfaces

New contract owners are proposed `.spl` paths; they do not exist merely because listed here. Names ending V1 identify the new static-condition protocol, not a reinterpretation of existing CCH1 schema1.

| Proposed owner | Contract |
|---|---|
| `src/compiler/00.common/static_condition/static_domain_v1.spl` | `StaticDomainIdV1`, `StaticMemberIdV1`, `StaticDomainCardinalityV1`, `StaticUniverseV1`, `StaticConfigV1`, member resolution/config validation |
| `src/compiler/00.common/static_condition/static_guard_v1.spl` | `StaticGuardIdV1`, `StaticGuardTableV1`, `StaticGuardLimitsV1`, immutable builder/evaluation/canonical codec |
| `src/compiler/10.frontend/static_condition/static_region_scan_v1.spl` | `StaticScanResultV1`, `StaticGuardedRegionV1`, `StaticScanLimitsV1`, lexical structural scanner |
| `src/compiler/30.types/static_condition_boolable_v1.spl` | shared Boolable conversion classification, pre-import admitted conversion descriptors |
| `src/compiler/00.common/cache_contract/guarded_dependency_summary_v1.spl` | versioned guard/reference/effect manifest and coverage, linked to existing summary/AST/source objects |
| `src/compiler/80.driver/static_condition/static_closure_v1.spl` | active requirement worklist and summary/source discovery boundary |
| `src/compiler/10.frontend/cache_artifact/guarded_tldr_projector_v1.spl` | canonical guarded public import synthesis/rendering |

Exact first-slice public API (Simple numeric wrappers use i64 storage if current compiler requires it; wire validates u16/u32 bounds):

- `static_builtin_universe_v1() -> StaticUniverseV1`
- `static_universe_validate_v1(universe: StaticUniverseV1) -> Result<StaticUniverseV1, text>`
- `resolve_static_member_v1(universe: StaticUniverseV1, domain_name: text, member_path: text) -> Result<StaticAtomV1, text>`
- `static_config_validate_v1(universe: StaticUniverseV1, selections: [StaticAtomV1]) -> Result<StaticConfigV1, text>`
- `static_atom_evaluate_v1(universe: StaticUniverseV1, config: StaticConfigV1, atom: StaticAtomV1) -> Result<bool, text>`

`StaticAtomV1(universe_digest, domain_id, member_id)` is a resolved positive membership predicate bound to a validated nonempty universe seal; NOT is a guard operation. `resolve_static_member_v1` populates this seal. `static_config_validate_v1` and `static_atom_evaluate_v1` reject an empty or different atom seal even when numeric IDs happen to match. All five API signatures above remain unchanged; the returned/accepted atom record now carries this provenance. `StaticDomainCardinalityV1` is OneOf or Set. Each domain definition holds numeric ID, canonical name, cardinality, sealed member records, and alias index. A member record holds numeric wire index plus stable provider identity and stable member identity. Builtin IDs are explicitly enumerated constants, never host discovery order. Extension IDs are assigned through a canonical sorted sealed mapping with collision validation; no truncated unchecked hash is an identity. Wire index portability is conditional on the bound universe digest.

The first-slice owned data records are frozen as follows (all collections are caller-owned immutable values at API boundaries):

- `StaticMemberDefinitionV1`: member_id, provider_id, stable_member_id, canonical_name, aliases, availability (Static, SealedComplete, Dynamic).
- `StaticDomainDefinitionV1`: domain_id, canonical_name, cardinality, members.
- `StaticUniverseV1`: schema, domains, universe_digest. `static_universe_validate_v1` derives/checks canonical order/digest and rejects inconsistent identities, conflicting numeric IDs or malformed providers. Empty input digest requests canonical construction; a supplied nonempty digest must match.
- `StaticConfigV1`: universe_digest, selections, config_digest. Construction occurs only through validation; atom evaluation revalidates provenance/bounds rather than trusting externally constructed records.
- `StaticAtomV1`: universe_digest, domain_id, member_id. IDs use dedicated wrappers, with a wire adapter validating u16/u32 ranges. Runtime atoms share immutable interned seal text or a retained immutable seal handle; constructing each atom must not allocate or hash a fresh copy of the seal.

The builtin manifest fixes OneOf for os/arch/abi/backend/mode/profile and Set for feature/capability/cpu. Profile is not a bag of feature switches: conflicting profile selections fail; `feature.vulkan` plus `feature.cuda` may both be selected. Board/product and further extensions require an explicit cardinality in sealed metadata. The implementation must publish the exact builtin table with its tests; it must not derive members by querying the host. At minimum the selected examples (windows/linux/freebsd, aarch64/riscv64/x86_64, llvm/vulkan, critical, vulkan/cuda/dynload, jit, avx2) resolve in their corresponding domains. Membership does not assert a target/backend provider is installed. Provider capability admission remains a later check. Compound legacy aliases such as unix normalize to a guard expression in the migration adapter, not to a fake second selected OS.

`StaticConfigV1` stores universe_digest, sorted selected positive atoms and config_digest. OneOf requires exactly one selection; Set permits zero/many. Reject duplicate, unregistered, dynamic and wrong-universe selections. Host OS is not implicitly substituted for requested target. Config/universe digests use canonical byte ordering and length-framed fields, not native text-pointer ordering or ambiguous concatenation.

Later slice APIs, frozen at names/semantics and refined with owning parser types before edits:

- `classify_static_boolable_v1`: typed condition -> StaticGuard, RuntimeCondition, or Invalid diagnostic. Ordinary Boolable conversion is not sufficient evidence of early availability.
- `scan_static_regions_v1(source, universe, limits) -> Result<StaticScanResultV1, text>`.
- `evaluate_static_guard_v1(table, guard_id, config) -> Result<bool, text>`.
- `canonical_static_guards_v1(table, roots)`: reachable canonical atoms/nodes plus remapped roots and digest.
- `active_static_requirements_v1(summary, roots, config, limits)`: exact active requirements or NeedsSemanticDiscovery; never silently succeeds with unknown coverage.

There is no public constructor that declares an arbitrary imported conversion dependency-safe. An approved conversion descriptor is compiler-known, total, deterministic, pure and already expressible in the guard algebra. Explicit Boolable user enums are usable at runtime; dependency-time use additionally requires that descriptor. This keeps semantics shared without arbitrary CTFE.

Binding rule: `classify_static_boolable_v1` receives resolved semantic bindings for ordinary `if`/body expressions. It returns StaticGuard for `os.windows` only if the resolved owner is the static registry predicate. If `os` resolves to a local variable or another value, matching source spelling is insufficient: preserve runtime condition/reference semantics and do not prune either dependency path from that spelling. Aliases require equivalent semantic owner proof. Structural `@when` resolves its restricted domain/member grammar directly in the pre-import registry namespace, not through runtime lexical variables; local shadowing neither changes its domain nor makes a runtime value admissible.

The canonical wire container stores the universe seal once. Its compact atom records contain only numeric domain/member IDs; decoding validates the container seal before constructing bound public StaticAtomV1 values. Do not repeat a digest in each encoded guard node or serialize a runtime pointer as identity. Domain/member wire widths remain u16/u32; guard indices are u32. Guard/member wire indices are bound to the serialized universe/table. Temporary builder or arena indices are local implementation details and must be remapped before serialization; they are not stable semantic identities and cannot be compared across hosts or independent arenas.
## Guard builder and canonical identity

IDs 0/1 mean FALSE/TRUE. A mutable builder is exclusively owned by one scan, then frozen. Fast conjunction records contain sorted positive OneOf selections, required Set members and negative atoms. Merge detects conflicts and deduplicates; OR/general negation promotes to hash-consed DAG. Nodes are Atom, Not, And, Or. Apply bounded identities, complement, idempotence, direct absorption, and OneOf contradiction; do not search for arbitrary Boolean equivalence.

Interning is a memory optimization. Persisted IDs must not depend on hash table order or allocation schedule. Canonicalize reachable nodes bottom-up with stable domain/member order and sorted commutative child structural keys; collision-safe compare full node structure. Encode references to topologically earlier canonical nodes and reject cycles, duplicate conflicting IDs, out-of-range references, depth/byte overflow and stale universe. Renderer respects not > and > or and emits stable provider-qualified spelling when needed. Equivalent normalized graphs yield identical bytes across hosts; semantically equivalent arbitrary formulas are not promised identical hashes.

No-condition fast path checks both directives and summary-relevant static-if need. Finding no '@' alone is not enough to skip required inline/generic body analysis. Reuse ordinary lexical analysis when available. Scalar truth evaluation uses config-scoped memo by guard ID; never reuse a memo with another table/universe/config.

## Structural scan and branch state

Scanner state: source offset, lexical mode, line map, current guard, bounded branch stack, local guard builder. Lexical mode handles escaped strings, raw/multiline strings, comments and language-supported interpolation. Delegate lexical boundary rules to existing owner helpers rather than invent incompatible quote counting.

Frame: parent_guard, taken_guard, saw_else, opening_span. Enter A => parent AND A, taken=A. Elif B => parent AND NOT(taken) AND B, then taken=OR(taken,B). Else => parent AND NOT(taken), forbid duplicate else or elif after else. End restores parent. Reject malformed parentheses, missing end and depth overflow. An inactive parent does not suppress malformed/unknown nested guard diagnostics.

Regions retain byte ranges and GuardId with original logical source identity; active view is a range iterator or offset-preserving projection. Diagnostic spans always reference original bytes. Do not allocate a full copy per branch. Deferred inactive syntax is framed but not AST/typechecked; complete portable AST consumers must check the syntax coverage tag.

## Import gate and error propagation

Current `_driver_entry_import_module_paths(content) -> [text]` cannot report malformed condition errors. Keep that compatibility helper for existing callers until migrated. Add a typed owner result at `_driver_cached_entry_source_scan`/`driver_source_pipeline_loading` boundary; production guarded closure must consume Result, not collapse Err to an empty list or broad import set. Both imports and sibling/reexport candidates retain guards. Evaluate a candidate before `_driver_resolve_entry_import`, numbered-path rewriting, existence checks or file discovery. Unknown static syntax is an error, not a fallback that loads both branches.

Path-only scan cache is insufficient once it contains selected import lists. Either cache only immutable symbolic scan by source/grammar/universe and derive selected lists separately, or bind selected cache entries to full config/policy digest. Preferred: symbolic cache plus target closure cache. Existing callers without an explicit config use one compiler-entry frozen config passed through the owner; do not query environment repeatedly in scanning.

## Summary, closure and TLDR

A new guarded profile references the existing validated PublicSummary/AST/source CAS objects, sealed universe and canonical guard table. Declaration/reference records carry GuardId and stable symbol IDs; required reference roles distinguish signature/layout, generic/inline/const/macro/advice body, executable body/link object, initializer/coherence/provider/FFI/reflection/test effect, and navigation-only. Navigation references never become executable dependencies merely by existence.

Coverage is explicit per reference/effect partition: Complete or NeedsDiscovery with reason. Cold structural scans can certify directive/import regions, but cannot infer complete arbitrary body references from tokens alone. The semantic owner completes those partitions from required parsed bodies. Legacy CCH1 schema1 stays readable with unknown guarded coverage; it cannot authorize aggressive pruning. Use codec registry/version negotiation and verified closure pins before admitting the successor.

For public TLDR, traverse public roots plus exposed semantic body requirements. Merge external `(owner,symbol)` guard with OR over path-guard AND reference-guard. Drop false edges, group by owner/canonical guard, resolve required owners, then render stable imports/declarations. Cycles use monotone worklist/SCC processing; store visited `(symbol, accumulated normalized guard)` with budgets. Concrete target closure uses boolean reachability per symbol/effect, so each admitted fact is expanded once. Budget exhaustion requests complete conservative discovery or fails explicitly; never emit partial TLDR as complete.

Initializer and unknown-effect module membership is retained according to current semantics until a complete producer proves absence. Ordinary unused private import omission is a public projection property, not blanket permission to suppress executable compile diagnostics. Required private body imports remain in executable/link manifests even when absent from displayed TLDR.

## Cache publication and change handling

Bind symbolic profile to source CAS digest, raw source witness, logical source identity where name resolution requires it, grammar/parser semantic producer, codec/coverage schema, Boolable policy, domain seal, and portable resolution/readset identities. Target projection adds explicit config and requested root/effect mode. Tool executable hash may remain an admission witness; never normalize it into a supposedly portable semantic producer without an established equivalence contract.

Keep two identities: source-validation witness changes on any source edit; semantic public digest changes only when exported/required semantic facts change. Revalidate/regenerate the witness before retaining an unchanged semantic digest. Object keys additionally bind MIR/body/readsets, backend/target/ABI/options and aspect/capture semantics. SMF uses distinct layer/codec/runtime-format identity even if sharing a canonical target-artifact storage container.

On changes, reverse semantic dependencies select affected consumers; object/link and interface edges remain separate. Guard/universe/config change recomputes affected selected closures, including formerly false edges. Aspect cut target changes invalidate woven facts and consumers even when source mtime is unchanged. Captured values use canonical typed value bytes or immutable versioned snapshots; unresolved mutable or address-bearing state is noncacheable.

Cache miss requests exact work only after current module TLDR/discovery identifies needed active requirements. Generation-bound outbox delivery may replay, but scheduler admission is idempotent. Publish interface only after retained validated summary/readset closure; publish object only after validated immutable OBJ/SMF and worker closure. Cancel/crash/stale lease settles waiters and fences old producers. The client never claims readiness from a cache filename, timestamp or unverified metadata flag.

## Diagnostics and migration

Structured diagnostics: E-STATIC-MEMBER, E-STATIC-DOMAIN, E-STATIC-AMBIGUOUS, E-STATIC-DYN, E-WHEN-NONSTATIC, E-STATIC-STRUCTURE, E-STATIC-LIMIT, E-STATIC-SEAL. W-STATIC-STRING and legacy cfg migration carry deterministic replacement spans only when unambiguous. An impossible valid guard may warn; an invalid guard never evaluates false.

Language policy version governs old enum/object truthiness and compatibility syntax. Introduce explicit builtin Boolable conversions with existing scalar behavior where retained; change enum acceptance only after diagnostics, repository migration and interpreter/native parity. A user method named bool alone does not establish trait implementation or static purity. Remove legacy syntax/duplicate seed logic only after pure-Simple/bootstrap parity, never to make an incomplete implementation appear consistent.