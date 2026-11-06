# Managed node attributes in Simple

Date: 2026-11-06. Status: architecture for implementation; no implementation PASS.
Scope: [selected full requirements](../../02_requirements/feature/node_attributes.md).
Evidence: [current source audit](../../01_research/local/node_attributes.md).
Authority: [consolidated design](../../03_plan/compiler/data/data_attributes_layout_containers_xray_2026-11-06.md).

## Decision

Introduce one opt-in logical node schema and access-place contract, shared by
compiler and interpreter consumers. Generate typed access operations over the
existing storage owners. Apply the feature to Simple's AST pools, analysis views
and BuildRunner task views through staged, executed integration. Ordinary field
syntax is the public interface; a runtime dictionary of untyped attributes is not.

Land this architecture and the [detail design](../../05_design/compiler/node_attributes.md)
before code. Land shared structural contracts before consumer changes. A foundation
PR or binary-node pilot never satisfies the full completion gate by itself.

## Current structure and reuse

`src/compiler/10.frontend/core/_AstExpr/nodes.spl` owns parallel expression arrays
and `expr_owner_*` accessors. Consumers must not import private arrays: the owner
documents a native-build copying hazard. Generation diagnostics exist, but do not
provide full pending/ready, deletion, authority or release lifetime guarantees.

`src/lib/common/structural/identity`, `tagmap`, `transfer` and `storage_layout`
already own shared structural contracts. Keep their frozen V1 formats unchanged.
Tag metadata can annotate schema/site identities; its fixed `TagValueType` cannot
replace exact language types. Existing adaptive containers/CollectionPlan remain
the index-policy owners. No new layout enum, scheduler or profile database is added.

HIR fields and interpreter lookups already exist. They do not yet implement the
managed-place contract. Field AOP selectors remain explicitly deferred. These are
integration gaps, not reasons to recreate the frontend or a second interpreter.

## Layer list and tree encapsulation

New paths in this table are **planned**, not present implementation claims.

| Layer/owner | Private implementation | Public-to-consumer surface |
|---|---|---|
| `src/lib/common/structural/node_attribute/` (new) | Descriptor validation, canonical schema reconciliation, lifecycle transition validation | Pointer-free schema/attribute IDs, descriptors, diagnostic facts and lifecycle contracts |
| `src/compiler/00.common/node_attribute/` (new) | Compiler symbol/type bindings and per-compilation intern tables | Typed resolved-property/place descriptors; links to existing type, effect and diagnostic owners |
| `src/compiler/10.frontend/core/` | SPL parser adapters, declaration extraction, existing AST arrays and constructors | Normalized declarations and generated owner facades; no sibling-private storage exports |
| `src/compiler/20.hir/`, `30.types/`, `35.semantics/` | Type/applicability resolution, definite initialization, AOP matching | Checked managed-place operations and obligations through existing HIR/semantic facades |
| `src/compiler/50.mir/`, `55.borrow/`, `60.mir_opt/` | Place projection, borrow/pin checking, representation eligibility | Typed lowered operations, admitted storage projections and immutable decision receipts |
| `src/compiler/70.backend/` and interpreter owners | Backend emission and engine-local value storage | Admitted typed access implementation and explicit unsupported capability diagnostics |
| `src/compiler/80.driver/` | Context assembly, build policy, worker dispatch | Frozen schema/policy snapshot and exact semantic/physical action identities |
| `src/app/` config/profile/LSP/BuildRunner owners | File I/O, user-facing explain, profile ingestion, scheduler state | Typed immutable inputs to compiler/common; owner-validated task transitions |

Frontend grammar stays single-source. Loader/interpreter consumers may use common
descriptors directly, not each other's private symbol or storage tables. Library
contracts cannot import compiler HIR, app profile readers or engine RuntimeValue.
Do not move private backend algorithms upward merely to make imports convenient.

## Common nodes and visibility matrix

Proposed common relative paths:

- `structural/node_attribute/schema_contracts.spl`: logical IDs/descriptors and provenance.
- `structural/node_attribute/schema_resolver.spl`: canonical declaration reconciliation.
- `structural/node_attribute/lifecycle_contracts.spl`: obligation/ready/retired transition facts.
- `compiler/00.common/node_attribute/property_contracts.spl`: compiler type and place bindings.
- `compiler/00.common/node_attribute/resolved_policy.spl`: references to existing physical plans and trace capabilities.

Each populated cell states **P** (public to its owner/parent facade) and **N**
(public to the next consuming layer). This is module API discipline, not new
visibility grammar. `read` means immutable contract access, never mutation rights.

| Raw layer | Schema descriptors | Lifecycle facts | Typed property/place | Resolved policy |
|---|---|---|---|---|
| Structural common | P: validate/resolve; N: immutable descriptor | P: validate; N: transition facts | — | — |
| Compiler common | P: bind exact type; N: read | P: bind obligation; N: read | P: construct checked descriptor; N: read | P: compose references; N: read |
| Frontend/AST owner | P: normalized declaration; N: common descriptor | P: reserve/finish/discard; N: checked handle | P: owner projection; N: logical field identity | P: selected context; N: read |
| HIR/types/semantics | P: resolve; N: read | P: prove obligations; N: checked facts | P: type/effect check; N: checked operation | P: eligibility facts; N: read |
| MIR/borrow/optimizer | P: read; N: identity | P: prove leases; N: admitted projection | P: lower; N: typed instruction | P: rank safe candidates; N: frozen decision |
| Backend/interpreter | P: read; N: cold maps | P: enforce; N: explicit failure | P: execute; N: typed result/event | P: capability check; N: receipt |
| Driver/app/tools | P: inputs/explain; N: frozen snapshot | P: owner validation; N: encoded facts | P: navigation/explain; N: source origin | P: load/freeze; N: immutable worker input |

## Opt-in and off behavior

Use a proposed versioned build configuration field `data_policy.node_attributes`
with values `off` and `enabled`; parser support is part of implementation. Keep
this distinct from per-schema `@node_tree(...)` and from trace activation.

`off` preserves ordinary classes, fields, allocation and existing AST execution;
it emits no managed helpers/tables or data-observer dependency for ordinary code.
An explicit managed declaration while off is an actionable error. Silently
interpreting it as an ordinary class would change its copy/identity contract.

`enabled` admits opted-in schemas only. It does not rewrite every class or enable
XRay. No runtime toggle may strip safety checks from existing managed handles.
For Simple's own compiler adoption, build two explicitly identified compiler
compositions until parity is proved; then promote the enabled composition through
the normal bootstrap admission flow. Disabling requires a new build/context,
never reinterpretation of live nodes or cache artifacts.

## Semantic and physical separation

A schema fixes exact nominal types, applicability, requiredness/defaults,
visibility, mutation authority, effects and dependencies. A physical plan fixes
row/column/sparse location and representation epoch. Schema changes are semantic;
physical changes are admitted only if the logical contract remains equivalent.

Canonical type identity comes from existing type resolution and includes package,
declaration, generic arguments and qualifiers. Library descriptors retain a
pointer-free exact identity; compact local IDs are indexes with checked context,
not equality proofs by machine width or short hash. No new competing type system
is created in structural common.

`NotInit<T>` is a must-resolve construction obligation. It is not `Option<T>` or a
wrapper around each field. Only stored initializer-writable members need state
bits. Computed dependencies and forwarded targets have their own readiness rules.
Neither profiles nor optional aspects can prove initialization, authority or bounds.

Qualified handles separate region incarnation, object/store identity, node
incarnation and physical epoch. Existing frozen entity/transfer formats are reused
where sufficient and wrapped/versioned where not. Do not silently reinterpret
`EntityRef` fields as lifetime generations. Owner APIs retain authority to mint,
validate and retire handles; a public tuple is not an authorization capability.

## Access, observation and storage

The semantic pipeline is declaration normalization → exact type/schema resolution
→ managed-place construction → effect/ownership/topology checks → static advice
→ admitted storage projection → optional observation of completed operations.
Reads, writes, initialization, RMW and lifecycle events retain different meanings.

Preserve the existing authoritative expression order or explicitly reconcile it
across engines before rollout. Nested assignment must update a real place, not a
temporary getter copy. Borrowed physical projections carry an admitted lease or
pin; they cannot survive an incompatible migration. A generated helper and its
backing loads do not multiply one logical get/set event.

Reuse `StorageLayoutPlanV1`, CollectionPlan and `.sprof`; unsupported combinations
are rejected. No raw XRay API in node owners, no schema lookup or strings in hot
callbacks, no migration in observers. Default application is next build, instance
or immutable snapshot. General shared live migration stays separately capability
gated under the source plan's transactional and progress requirements.

## Simple adoption and completion

First integrate binary-expression construction, source span, children and operator
through existing AST owner accessors. Keep the internal discriminator and legacy
codec until all consumers have a verified equivalent. Expand to real traversals,
other expression/statement/declaration families, HIR analysis sidecars and
BuildRunner task views. Owner access protects scheduler/result admission; public
property writes cannot mark a task successful.

Full completion requires ordinary source syntax and SDN equivalence, compiler and
interpreter parity, mandatory lifecycle checks, field AOP, capability-honest
observation, cache/LSP integration, actual Simple adoption and off/on evidence.
The [delivery/test plan](../../03_plan/sys_test/node_attributes.md) separates these
gates. Reference storage, parser acceptance and authored tests do not prove native
integration. No production PASS is claimed by this architecture landing.
