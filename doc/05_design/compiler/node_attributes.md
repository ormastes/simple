# Node attributes: detail design and structural handoff

2026-11-07 implementation follow-up: use the
[canonical V2 contract extension](data_schema_v2_contract_extension.md) for
explicit views/property semantics. Its outer digest identifies the complete V2
schema; the embedded V1 projection must not be treated as V2 lifecycle proof.
The [program matrix](../../08_tracking/data_attributes_program_progress_2026-11-07.md)
retains all remaining integration and execution gates.

Date: 2026-11-06. Status: implementation design, not shipped APIs.
See [architecture](../../04_architecture/compiler/node_attributes.md),
[requirements](../../02_requirements/feature/node_attributes.md), and
[source plan](../../03_plan/compiler/data/data_attributes_layout_containers_xray_2026-11-06.md).
All new names below are proposed contracts until implementation and admission.

## Shared contract inventory

| Contract | Contents and owner |
|---|---|
| `NodeSchemaIdV1` | Exact schema namespace/owner identity plus version; compact IDs valid only within the frozen schema context. Structural common. |
| `NodeAttributeDeclV1` | Canonical name, exact resolved type identity, applicable views, stored/computed/forwarded kind, required/default policy, authority, visibility, effects/dependencies and declaration provenance. Structural common, with compiler type binding. |
| `NodeSchemaV1` | Canonically ordered attributes/views and dependency edges, semantic digest and retained provenance. Immutable after resolution. |
| `NodeSchemaResolutionV1` | Either one complete valid schema or diagnostics with both conflicting declarations. No usable partial schema after failure. |
| `NodeConstructionFactsV1` | Required/assigned slots and computed dependency facts for the semantic checker. These are facts, not public minting authority or an owned-resource container. |
| `NodeHandleV1` | Qualified context, region/store/node incarnation and typed view binding. Minted only by a storage owner; projected references additionally bind the representation epoch/lease. |
| `ManagedPropertyPlaceV1` | Original site, exact type, receiver/index temporaries, access mode, mutation authority, borrow/effect/topology facts and owner projection. Compiler common. |
| `ResolvedNodePolicyV1` | Schema and existing layout/collection plan references, capability set, application mode, provenance and independent digests. Compiler common; driver freezes it. |

Do not export `RuntimeValue`, native pointers, AST pool arrays or compiler HIR
objects through the structural contract. Do not change frozen identity, TagMap,
storage-layout or transfer V1 field meanings. New contract validation precedes
consumer wiring, but an isolated contract library is not full feature completion.

## Resolver algorithm and configuration

1. Driver loads explicit SDN inputs through the existing config owner and verifies
   their module/build authority. Frontend extracts SPL declarations and explicit
   introduction manifests with original source locations.
2. Existing name/type resolution produces exact canonical type keys. Aliases
   normalize; distinct nominal types remain distinct. Unresolved/ambiguous type
   names fail before schema generation. Never compare unqualified type spellings.
3. Group declarations by exact schema owner and canonical attribute name. Sort
   deterministically; reconcile duplicate declarations by semantic equality, not
   order. Preserve all provenances. Applicability may union across distinct views
   only when type/requiredness/default/effect/authority contracts agree; conflicting
   declarations for the same property fail with both locations.
4. Validate view membership, defaults, computed/forwarded dependencies and owner
   visibility. Detect dependency cycles unless an explicitly admitted construction
   group contract handles them. Getter-only properties have no invented setters.
5. Assign deterministic schema-local IDs after canonical ordering. Cache identities
   use exact normalized semantic content and versioned digests, not incidental
   source order, timestamps or unchecked short hashes.
6. Resolve physical constraints separately. Hard constraints intersect; source/build
   pins conflict explicitly; profile preferences rank only eligible `auto` choices.
   Freeze the result per compilation before worker dispatch.

The proposed off/enabled build option belongs to the existing data-policy
envelope. SDN is the default external configuration format; JSON remains explicit
interoperability only. Off-mode managed declarations fail; normal declarations
take the preexisting path without loading generated schema tables.

Cold resolution uses sorted declaration groups and indexed dependency validation.
Ready access uses bound numeric IDs and a qualified projection. No text-key lookup
or SDN parsing is added to field-access hot paths. Re-resolution occurs only when
the exact semantic inputs change, not once per field or request.

## Construction and retirement state machine

States: reserved pending → ready → retired. Pending may instead be discarded.
There is no transition from retired back to ready under the same incarnation.

Reservation allocates a slot under owner authority and creates one must-resolve
obligation. It cannot publish a dereferenceable ready handle. Initializer writes
type-check and commit once; duplicate assignment fails without replacing/dropping
the prior owned value. Computed fields do not receive assignment bits.

Use a **retaining finalizer**: `try_finish` succeeds by consuming the builder and
producing a ready node; failure returns the still-owned builder with diagnostics.
A failed attempt cannot be propagated with plain `?` while abandoning that
obligation. A separately named consuming helper may discard on failure, but must
make that cleanup behavior explicit. Compiler definite-initialization and runtime
checks agree on this distinction.

Finish applies defaults only to unset stored fields, in a deterministic dependency
order. Each successful default is committed and recorded before proceeding; retry
does not execute it again. A failing default must obey its declared effect/error
contract. Validate all required fields, dependencies, authority and topology
before publishing. This is one whole-node/group validation, not a scan on reads.

Discard/cancellation releases each initialized owned member exactly once and
consumes the obligation. Ordinary unresolved drop is an error. Ready removal is
a different operation: check incoming edges and owner mutation rights, retire the
slot, and invalidate its generation. Generation exhaustion retires storage rather
than wrapping. A failed delete retains the ready node unchanged.

SCC/group construction can reference pending IDs only inside the group. It
publishes every member together after completeness/topology validation; it cannot
smuggle pending handles into an otherwise ready graph. Later-phase analysis uses
typed sidecars/result readiness, not uninitialized advertised core fields.

## Managed places and generated operations

Preserve the receiver, indices and RHS as explicit evaluated temporaries. Bind
field identity and exact type before storage lowering. Generated operations are
marked semantic artifacts with source origin so cleanup tools and LSP do not
erase them as trivial wrappers or navigate only to generated filenames.

| Operation | Required lowering |
|---|---|
| Read | Validate handle/view/authority, project admitted storage, preserve copy/borrow/move behavior, report one completed logical read. |
| Assignment | Evaluate once in agreed language order, validate writable place, commit one typed update, then report success. Failure emits no successful-set event. |
| Compound update | One receiver/place; one read and one write, or explicitly typed atomic RMW with its own event contract. |
| Nested/indexed mutation | Maintain a writable place chain and bounds/topology checks. No discarded temporary or unjustified copy-back. |
| Field borrow | Issue an admitted pin/lease or reject; outstanding incompatible projections prohibit conversion. |
| Init/finish/discard/remove | Distinct construction/lifecycle operations, never fake get/set of uninitialized or migrated values. |

Current assignment-expression evaluation in the Pure-Simple helper is RHS-first.
Before choosing a cross-engine contract, inspect the language specification and
all active evaluator/lowering paths and add side-effect ordering fixtures. Do not
silently change ordinary-language evaluation order to simplify managed access.

Use one internal property operation adapter for both Pure-Simple access evaluator
paths. The Rust bootstrap/reference path must agree semantically or reject the
feature explicitly until its adapter is admitted; a Rust-only implementation does
not qualify Simple support. New production ownership/generation logic stays SPL.

## AOP and observation

Resolve `get` and `set` against canonical logical field symbols, including
configuration-generated declarations. Keep `attr(...)` as annotation metadata
selection and repair its actual matcher separately within the same integration.
Whitespace/Boolean/malformed-selector tests cover the tokenized parser, not a
substring extractor. Unsupported forms fail explicitly rather than matching none.

Default helper exclusion prevents logical access plus generated function plus
backing-map advice from counting three times. Static semantic advice retains its
normal effect/ordering/cache contract. Optional observers cannot disable safety,
reenter mutation, throw through a trampoline, block or trigger migration.

Attach field/schema/site/epoch identities to the shared trace facade and existing
`.sprof` owner through a negotiated extension. No direct XRay calls from node APIs.
Compiler execution, interpreted program, compiled program and BuildRunner remain
separate profile domains. Counter-provider evidence is labeled as such. A combined
native-layout/XRay claim requires a combined producer/backend/provider test.

## Compiler adoption sequence

| Landing | Concrete change | Exit evidence |
|---|---|---|
| L0 | This architecture/design, selected requirements, current-state audit and test/delivery plan | Reviewed documentation PR, no implementation PASS claim |
| L1 | Shared structural schema/lifecycle contracts and resolver; compiler common bindings and off/enabled context | Exact typing/conflict/authority/determinism tests and layering review; no consumer rewrite before contracts land |
| L2 | Generated binary-expression view/builder over existing AST owners; source-span/child/operator access, sparse analysis result | Real parser/traversal uses the adapter; readiness, stale handles and direct/column/sparse parity; off-mode baseline preserved |
| L3 | SPL/SDN declaration integration, HIR/MIR places, borrow/initializer checks and both interpreter contracts | Real ordinary-syntax fixtures, nested writes, effects/order/moves/default failures, native qualification |
| L4 | Field AOP, shared observation/profile extension, cache/LSP explain and invalidation | Exactly-once events, unsupported-provider refusals, profile identity/loss and cache tests |
| L5 | Broader AST/statement/declaration and HIR adoption; BuildRunner owner views and worker receipts | Self-hosted compiler workload and runner DAG/result checks, admitted off/on comparisons |
| L6 | Full requirement audit and separately admitted physical/native/migration expansion | Every applicable requirement has source-matched executed evidence; no pilot-only completion |

L2 is intentionally a concrete use in Simple, not a standalone sample store.
Keep the owner arrays and existing discriminator/codec until their consumers are
migrated. Generated code may use already-supported language constructs during
bootstrap, but generation must be deterministic and must not require the feature
before the bootstrap producer can compile it. No seed fallback for qualification.

## Cache and diagnostics

Keep schema, physical plan, instrumentation plan, consumed profile and resolved
policy identities separate. Schema introductions affect semantic/TLDR surfaces;
private layout changes affect physical artifacts; changed consumed plans affect
action keys. Runtime object allocation does not churn semantic caches.

Diagnostics carry owner, schema/field identity, expected/actual type or state,
original source/config provenance and rejected capability. Do not allocate a new
numeric E-code range without checking the diagnostic owner. Planned categories:
disabled feature, schema conflict, unauthorized declaration/write, incomplete or
duplicate initialization, unresolved obligation, stale/wrong-view handle,
incompatible projection, topology violation and unsupported backend/provider.

## Failure and evidence policy

Existing cached AST formats stay unchanged until a separately versioned codec is
implemented. Decode rebinds fresh runtime ownership; serialized generations are
not transferable mutation authority. Before publication, failed conversion leaves
the old root authoritative; after publication, rollback needs a new validated
transition. Move-only recipes require reversible transfer or an explicitly
infallible/non-cancellable commit phase.

The first landing is documentation only. Executable SSpec scenarios and generated
manuals are implementation deliverables; this PR adds no placeholder passing
tests and claims no generated manual. Runtime admission, exact output/test counts,
coverage, core/MCP smoke and performance remain required before full completion.
