# Extreme typing and traceability: detail design

Status: proposed implementation contracts, 2026-11-01. Read the
[architecture](../04_architecture/extreme_typing_traceability.md) for ownership
and [selected policy](../02_requirements/feature/extreme_typing_traceability.md)
before this document. Identifiers here name proposed interfaces; they do not
assert existing functions or executable CLI support.

## Contracts and algorithms

| Proposed contract | Required data and invariant |
|---|---|
| `PublicSurfaceGraph` | Compilation subject, compiler/type-universe ID, effective export root IDs, canonical type nodes, visibility paths, substitutions, generated origin chain and completeness. One authoritative graph per publication candidate. |
| `TypeIdentity` | Compiler-owned stable-in-subject identity plus nominal declaration identity and instantiated arguments; never equality by pretty-printed spelling. Cross-revision matching records uncertainty. |
| `ExposureResult` | Safe / Violates / Unknown; export-to-leaf paths, canonical leaf, spans, surface digest and policy digest. Multiple diagnostics deduplicated by root/type/path identity. |
| `AssuranceRulePolicy` | Existing resolved assurance policy plus named `extreme_public_api` version, builtin catalog, domain-bound semantics, unknown handling and gate disposition. |
| `PublicationDecision` | Candidate/engine/policy/surface identity, check phase, allowed/denied/unknown, diagnostics and cache evidence. Public record fields alone do not establish unforgeable authority. |
| `TraceSnapshotIndex` | Snapshot/generation/schema/rule identity; nodes by ID/kind, forward/reverse typed adjacency, semantic symbol references, validity/completeness diagnostics. |
| `TraceQueryV2` | Operation, snapshot, roots, direction, allowed relations, precision filters, depth, limit, cursor and trusted visibility context. |
| `TraceViewProjection` | Canonical selected ID, subject, ordered rows/edges, annotations, paths, counts, omitted frontier, provenance and independent page/graph/qualification states. Pure computation. |
| `CodeRelationFact` | Compiler symbol endpoints, relation kind, exact/bounded_set/heuristic/unknown, static/observed distinction and expansion provenance. |
| `WorktreeOverlay` | Registered session identity+generation, immutable base/head/index/dirty subjects, capture state and typed semantic deltas. |

Exposure processing resolves export closure first, then substitutes canonical
types. DFS/SCC processing memoizes `(TypeIdentity, substitution, boundary,
policy)`; a processing set identifies cycles without declaring them safe.
Strongly connected transparent aliases without a resolved base are Unknown.
Recursive nominal types may be Safe only after all observable members and
generic arguments satisfy the policy. A compiler-trusted opaque marker stops
private representation traversal, not traversal of exposed operations.

Check explicitly public and implicitly exposed signatures alike: synthesized
constructors/accessors, equality/comparison/operator hooks, inherited/forwarded
methods, conversion/unwrap views, trait defaults and associated types. Raw
bool/text returns from derived public methods violate the selected rule.
Compiler-private intrinsic operations are outside the external API root set.
Only compiler identity establishes a builtin or nominal boundary; casing and
alias spelling are irrelevant. Unresolved external types, truncated expansion
or missing generic guarantees produce Unknown. Diagnostic traversal has
separate node/edge/path-size limits; robust+ Unknown denies publication.

Build candidate engine state without running user code. Analyze resolved
exports, expand/weave, specialize, analyze any changed/generated surface, then
commit the artifact or activate the module. Driver, loader and interpreter
adapters supply the same typed policy. Cache a decision only when compiler,
type-universe, source/dependency surface, generation, policy and engine ABI
digests match. A weaker-policy cache result is never reused as robust evidence.

## Easy semantic type creation is a delivery gate

Existing design documents specify `newunit Name: Base as suffix` in
[world units/newunit](language/language_features/types/world_units_newunit.md).
The parser's `core/_ParserDecls/enum_module_body.spl` registers newunits through
`core/types.spl:newunit_register`; registry/reset specs exist. These are source
observations, not proof that literal lowering and all execution engines work.
The system spec's historical RED note must not be relabeled as a current run.

E3 must demonstrate declaration, typed literal resolution, range diagnostics,
distinct nominal identities, import/reexport, container/callback use and actual
engine execution. Compile-time typed literal conversion does not require a
public function taking a raw primitive. Keep storage private and expose only
domain-safe operations; a generated primitive getter or raw constructor is a
bug. Use measurement units for real dimensions; use nominal newunit/opaque
types for identities and statuses. Do not prescribe wrapping `Option<i64>` as
a solution because its leaf is still bare. Text/char/bool ergonomics need real
semantic construction cases, not an untested numeric-only migration story.

## Query and storage behavior

Snapshot extraction is effectful; querying is pure. Publish a new index
generation only after validating IDs, relation endpoints, contains acyclicity,
symbol references and completeness diagnostics. Keep the last valid generation
on interrupted extraction, visibly marked stale. Missing/unauthorized content
is not an empty graph and cannot satisfy obligations.

Build adjacency in O(V+E), sort once by stable relation/endpoint identity and
retain reverse maps. Bounded BFS costs O(visited vertices + visited edges);
high fan-out hits an explicit work limit. Return one deterministic shortest
path for `path`; a bounded path set may be a later explicit mode. `walk`
returns typed reachable facts, `impact` explains reverse dependency paths and
`gaps` reports missing declarations, unknown resolution or unqualified
obligations separately. No command infers a verified result from a link.

Cursor payload is versioned SDN or an opaque encoding of that contract, with
a query digest and continuation position/frontier token. The digest includes
snapshot, generation, operation, roots, relation/direction/filter/precision,
depth, page size, visibility policy and deterministic order version. Validate
before allocation or lookup. Cross-user remote adapters derive visibility
context from their trusted caller boundary; the client cannot self-assert it.
An in-process record is not a security capability merely because it is typed.

Paged node views may include induced edges, but label that limitation. Full
graph export pages node records and edge records independently with stable
IDs and validates all endpoints after reconstruction; never lose cross-page
edges. Qualification operates on the admitted graph/evidence scope, not on a
rendered slice. Hidden counts may themselves need redaction.

Schema migration dispatches explicitly by version. Keep v1 graph/declaration
readers, version new nodes/relations and reject unsupported writers. Import
legacy grouping with source path/digest, old/new identity and explicit mapping
provenance; ambiguous identity is a diagnostic. `contains` cycle checks cover
cross-file and nested groups, independent of manifest placement.

## Report, code matrix and adapter behavior

CLI proposed commands are listed in the [TUI sketch](extreme_typing_traceability_tui.md).
Table is human default; `--format=sdn` is the structured contract. JSON is an
explicit interoperability adapter, never an internal replacement store.
Markdown/HTML use the same projection and explicit `--output` destination.
Sort by stable identity, omit volatile generation timestamps from structural
content, and put freshness/provenance in a separately identified run context.
Use atomic destination writes, safe relative source links and no script/remote
resource execution. Sanitize before serialization and rendering; validate
file URL/path schemes, traversal, symlinks and output collisions.

Feature/layer cells hold sets of semantic symbols and membership provenance.
Dependency cells hold sets of directed code relation identities plus precision
counts. Shared symbols count once in each set; totals use union. Preserve
unknown membership and unresolved call counts. Neither a zero visible cell nor
an omitted private cell proves no dependency.

LSP/MCP adapters expose bounded queries, cancellation and explicit stale/resync
responses. Reuse immutable index generations and caller authorization. The
editor's unsaved buffer can be a separately captured snapshot, never silently
joined to staged/Git facts. Slop handles layout/focus only. Caret compares
registered snapshot sets without spawning Git per pane refresh. PR refresh is
an explicit effect with cached freshness; offline unavailability is visible.

## Query authorization and cache freshness clarification

Cursor binding includes effective caller identity, allowed scope and
authorization epoch, not just a shared policy name/version. Authorization
filters root lookup, traversal intermediates, returned edges, counts, frontiers
and diagnostics before projection. A bounded path search with an unexplored
frontier returns incomplete/unknown instead of "no path".

Compiler verdict caches bind deterministic semantic/source/policy/type/target
inputs and invalidate on changes; no arbitrary wall-clock expiry is required.
External admission/evidence and PR metadata have separate trust/freshness
policies. Native graph interfaces remain SDN; any JSON facility is a separately
requested external interoperability adapter.

## Errors and qualification

Stable categories: invalid query/cursor, missing entity, incomplete capture,
stale generation, unresolved semantic type, forbidden export, unsupported
schema, budget exhausted, unauthorized material and unavailable provider.
Keep diagnostics bound to subject/rule/entity/provenance, and preserve the
last valid display without presenting it as current green.

Evidence admission remains separate from pure eligibility. Current
`evidence.spl` compares a supplied trusted context but does not independently
certify producer or artifact bytes. A `PublicApiSurface` fact or API violation
record is source evidence, not proof of an executed check. Proof obligations
must bind actual production IR/transform versions and durable reviewed proof
artifacts; unsupported properties remain blocked. See the test and phase plans
for deliberate-red, engine-parity and qualification gates.

## E1 retained signature observation candidate (2026-11-02)

The first source slice adds `00.common/api_signature_facts_v1.spl` flat records
and `30.types/type_infer/api_signature_projection_v1.spl`. The production
`hir_typecheck_consumer_v1` projects while its actual HM context is alive when
the retained typecheck pass requests collection. Primitive kind variants,
container/callback edges and declaration owner plus module-local SymbolId are
preserved without text classification. Bounded substitution following reports
cycles/unresolved variables. The unannotated-return sentinel remains Unknown.

The projection retains only scalar/enum/text/array records. Immutable text
values are retained by value, not through HIR roots; transient consumers must
promote the returned record before reclaiming scratch. Existing archive body
leases do not request collection and their receipts default to absent facts;
their diagnostic digest/admission contract is unchanged. A dedicated authored
spec promotes only the projected records then reads them after scratch ends.

CompileContext stores at most 256 modules / 16384 nodes. Each projection has
at most 128 callables / 1024 nodes / depth 32; identity text lengths are bounded.
Compile entry and every retained typecheck pass clear the preceding generation.
Repeated module publication replaces its previous row and adjusts the budget.
Missing means NotCollected. Collection follows the existing profile/env-gated
typecheck path and is absent from cached/no-op/streaming paths, not silently
complete. Performance targets remain unmeasured.

These are incomplete observations: effective export closure, generic domain
guarantees, nominal public operations, non-callable/generated surfaces and all
engine admission remain explicit unknowns. No fatal rule or Safe verdict is
introduced. E1 and E2 remain unfinished. New execution/negative specs are
authored but unrun because a source-matched admitted runtime is unavailable.

## E1 frozen export-route join candidate (2026-11-03)

`20.hir/hir_lowering/api_export_route_projection_v1.spl` now joins frozen
export-origin/declaration-authority rows to the preceding callable observations.
`run_typecheck_warn_pass` receives the actual retained registry explicitly from
HIR lowering, binds each freshly collected signature to its physical source,
and retains one flat route projection in CompileContext. Compile/pass entry
clears it; the existing retain-products path preserves it. No registry means
NotCollected. Archive leases and cache admission remain unchanged.

Each witness records exporter and terminal physical index/canonical path,
registry generation, alias/source names, declaration visibility and the joined
module-local SymbolId. Generation/index are process-local, not durable identity.
An exact join requires both authority rows and export origin to agree on the
same physical declaration and exactly one captured callable to match. Missing,
stale, malformed, duplicate or conflicting observations remain Unknown.
`Joined` means callable identity linkage only: even a public declaration retains
`ancestor-visibility-not-collected`, because directory/module ancestry is not
supplied by this surface contract. Nominal/private representation is unchanged.

Bounds: 4096 physical surfaces, 16384 aliases, 16384 authority rows, 4096 routes,
256 captured modules and 128 callables per module. The binder canonicalizes one
source path and scans the bounded physical array once per captured module; the
projector builds alias, authority and callable indexes once. It never rescans
the registry per callable or route. Metadata lengths and existing signature
node limits bound retention; over-budget projection returns explicit truncation.
No filesystem tree scan, initializer, or publication gate is introduced.

Authored route specs exercise real parser/surface/inference owners and negative
identity cases. Execution and measured performance remain pending the admitted
runtime. This slice does not complete effective export closure, E1, enforcement,
generated-surface coverage or cross-engine parity.

## E1 structural exposure walker (2026-11-06)

`30.types/type_infer/api_exposure_walker_v1.spl` adds `walk_api_exposure_v1`,
a pure function over one retained `ApiSignatureFactsV1` that returns the
`00.common/api_exposure_result_v1.spl` records. It consults no HIR, symbol
table or substitution and makes one O(n) pass. Retained facts are trees by
construction (every parent precedes its child), so no SCC/memo table is built
until nominal members are projected; that is stated, not deferred silently.

Per callable: every reachable Integer/Float/Bool/Text/Char leaf is `Violates`
with the full node path and ordinals (return is -1), including leaves under
Optional/Result/Tuple/Union/Array/Slice/Dict, callback parameters and returns,
and Reference/Unique/Shared/Weak/Isolated wrappers. A node carrying any
projector reason (nominal members, generic guarantee, pointer/any exposure,
unresolved inference, cycles, budgets, effects) is `Unknown` with that reason;
Pointer and Any stay a separate unsafe class and are never folded into the
primitive rule. Nominal generic arguments are still walked. Findings are
unique by (callable, leaf, path) because each node is visited once.

Fail-closed invariants: a parent index at or after its child, an out-of-range
or shared signature root, a root that is not a Function, an unclaimed root, a
callable without exactly one return slot, a path deeper than 64, or an
Unknown/Pointer/Nominal node with no reason all yield `facts-malformed`; every
callable in that module becomes Unknown and no finding is emitted from
poisoned facts. More than 16384 nodes returns a truncated Unknown result
without walking. The module verdict is `Violates` when any callable violates
and otherwise `Unknown`; `Safe` is unreachable because
`effective-export-closure-not-collected` is always recorded. `declared_visibility`
is carried for consumers and never used to skip a callable.

Spec `test/01_unit/compiler/type_infer/api_exposure_walker_v1_spec.spl` covers
hand-built facts and the production projection of a parsed module; it was
RED (missing module) then GREEN (6/6) on the seed runner, with a mutation
(dropping Text from the rule) failing 2 cases. No diagnostic, named rule,
CompileContext retention or engine admission is introduced; E1 remains
incomplete on effective export closure, nominal members and generics.

### Retained walker results (2026-11-06, follow-up)

`publish_module_typecheck_receipt_v1` classifies exactly the facts it retains
and stores the `ApiModuleExposureV1` row in `CompileContext.api_exposure`,
keyed by module name. A module whose facts are not retained (budget,
empty name) gets no row, so a missing row means NotCollected. Republishing a
module replaces its row; `run_typecheck_warn_pass` entry and `compile()` entry
clear the map together with the facts. Nothing consumes the rows yet: no
diagnostic, named rule or admission decision is derived from them (E2).

### Route join defects fixed (2026-11-06)

Executing the route spec exposed two production defects, fixed in code: (1)
`module_surfaces_freeze` set `surface.frozen` and `export_origin_index.frozen`
but never `declaration_authority_index.frozen`, so
`module_surface_declaration_authority_lookup` could never find a row and the
route projector reported every surface as `surface-index-malformed`; (2)
`collect_module_typecheck_receipt_v1` retained facts under the parser's
filename-derived `HirModule.name`, while the registry aliases, the driver's
module map and the receipt's own diagnostics use the pass's logical module
key, so no alias could join. Facts are now keyed by that logical name;
`module_path` still carries the file path. Route spec 3/6 -> 7/7 on the seed.
The production join inside a real `compile()` remains pending Phase 3.

## E2 named rule and publication guard (2026-11-06)

`00.common/api_publication_decision_v1.spl` projects the resolved assurance
strictness onto the named rule `extreme_public_api` (REQ-EAPI-003): advisory
at moderate, warning at strict, denial at robust/critical/verified; an
unrecognized profile name fails closed to denial. `decide_api_publication_v1`
is pure over `CompileContext.api_exposure` and the frozen export routes. Its
root set is every `Joined` route's terminal callable, deduplicated by
(terminal module, local symbol). Unjoined callables, private locals and
unresolved routes are neither Safe nor denied (REQ-EAPI-001). A joined root
whose module has no exposure row, or whose symbol is missing or ambiguous,
is an unknown root with an explicit reason.

Denial applies only to `Violates` roots. **Unknown denial is deferred**: every
module still carries `effective-export-closure-not-collected`, so denying
Unknown would deny every build; this is recorded as an open E1 obligation,
not a policy exception. Diagnostics name exporter, export, terminal callable,
leaf kind and the return/argument path.

`80.driver/driver_api_publication_guard_v1.spl` applies the disposition on
its own rule code (errors at Deny, warnings at Warn, nothing at Advisory) and
stores the decision in `CompileContext.api_publication_decision`, cleared with
the facts. `driver_orchestration` evaluates it once at phase-5 mode dispatch
before interpret/JIT/AOT and returns `TypeError` on denial, so no engine runs
user code or emits an artifact. The typecheck pass's own warning policy is
untouched (no global robust escalation).

Activation is explicit: `SIMPLE_EXTREME_PUBLIC_API=1`. The stdlib is not yet
migrated (E3), so an always-on robust denial would reject every robust build;
activation order is migration policy (plan: "migration affects
activation/order, not rule exceptions"). When active, the retained typecheck
pass runs at every profile so advisory/warn rows have facts, and the native
no-op admission and cached-SMF interpret route are refused at a denying
profile rather than bypassed (owner audit step 4). Staged AOT flush / AOP
recheck of generated exports (AC-EAPI-005) and REPL/dynload parity (E4) are
not covered by this slice.

**Temporary warn-only default (2026-11-07, owner decision "warn in temp").**
With `SIMPLE_EXTREME_PUBLIC_API` unset the rule runs at every profile in a
warn-only mode: violations and Unknowns become warnings (one summary warning
per exporter module; `SIMPLE_EXTREME_PUBLIC_API_VERBOSE=1` lists each), the
decision is never `allowed=false`, and cached SMF / native no-op admission is
not refused. `SIMPLE_EXTREME_PUBLIC_API=1` keeps the profile dispositions
(deny at robust and above); `SIMPLE_EXTREME_PUBLIC_API=0` turns the rule off.
This is temporary: the default flips to deny at robust once the E3 stdlib
migration lands (drop `extreme_public_api_warn_only_v1`).

Spec `test/01_unit/compiler/driver/api_publication_guard_v1_spec.spl` (7
cases) covers the disposition ladder, inactivity, joined-root denial at
robust/warn at strict, private-local exclusion, unknown roots, cached-admission
refusal, and the production route fixture through the driver guard. It ran
7/7 on the seed; a mutation disabling denial fails. The full `compile()`
choke point is verification-pending on a self-hosted binary.

## E1 effective export closure (design, 2026-11-06)

Status: design handoff for the next code slice; nothing below is implemented
by this section. It defines the one structural fact E2 still lacks: which
retained callables are *effectively exported* from the compilation subject, so
that a module verdict can become `Safe` and Unknown denial can activate.

### Subject and model of record

The closure is computed over the frozen `ModuleSurfacesByName` registry of
one compile together with the retained signature facts and the frozen
export-route facts. It is relative to that compilation subject: a facade that
is not part of the compile is unseen, and the result says so rather than
guessing. The visibility model of record is
`00.common/dependency/visibility.spl` (Lean `VisibilityExport`): a declaration
must be explicitly exported to be visible externally (`must_be_exported`), and
nothing inside a child file can be more public than its directory manifest
allows (`private_module_restricts`). Two facts about the current compiler
bound what the closure can observe:

- Export-origin rows exist only for explicit `export` / `export use` items
  (`module_surface_export_index.spl` iterates `surface.exports`). A bare
  `pub fn` with no export statement has no route and is therefore
  `NotExported`; `pub` alone is a declaration shortcut, not publication.
- The compiler frontend (`10.frontend/ast.spl`, `parser_types.spl`) has no
  `mod` / `pub mod` node; only the interpreter loader's manifest reader
  (`99.loader/module_resolver/manifest.spl`) parses them. A facade therefore
  publishes through `export use` only; `pub mod` is not observable from the
  frozen surface and is recorded as a model gap, not emulated.

`35.semantics/visibility_checker.spl` treats `Visibility.Public` as visible
everywhere and knows no ancestor chain. The closure follows the model of
record, not the checker; it changes no W04xx diagnostic. The divergence is
named here so that nobody reads a `NotExported` closure entry as a visibility
error or a `Public` declaration as closure membership.

### Definition

For a retained module `M` bound to physical surface `p`, the *ancestor facade
chain* is, for every proper dotted prefix `P` of `M`'s logical name (for a
facade `X.__init__` the prefixes are those strictly shorter than `X`), the
registry surface aliased by `P.__init__` (or by `P` when that alias resolves
to a surface whose canonical path ends in `__init__.spl`), nearest first. A
prefix with no facade surface in the registry is not a boundary and does not
restrict, exactly as `checker_nearest_boundary_dir` treats a directory without
`__init__.spl`; `src/lib` has no `__init__.spl`, so stdlib leaves publish by
their own `export` list.

A retained callable `(p, local_symbol, name)` has exactly one closure status:

| Status | Rule |
|---|---|
| `Exported` | `M` has a `Joined` direct route (exporter `p`, terminal `p`, source `name`) **and** every facade in the ancestor chain has a `Joined` route whose terminal is `(p, name)`. The outermost such exporter is the *root exporter*. |
| `NotExported` | No direct route for `name` exists, or some ancestor facade has no route whose terminal is `(p, name)`. The first missing exporter is recorded. |
| `Unknown(reason)` | The direct route or an ancestor route exists but is not `Joined`; the route's own unknown reason is carried. Also when `M` has no retained facts, no surface binding, or the registry/route facts are missing, budget-truncated or malformed. |

Routes are looked up once by `(exporter index, terminal index, source name)`
over the bounded route array (4096 routes, 256 modules, 128 callables per
module, chain depth bounded by 32 prefix segments). No HIR, symbol table or
filesystem is consulted; no new registry pass is introduced. An outer facade
whose re-export resolves to a middle facade instead of the terminal is
`Unknown` with that route's reason (`export-authority-mismatch`), never
`NotExported`.

### Records and placement

- `00.common/api_export_closure_facts_v1.spl`: `ApiExportClosureStatusV1
  {Exported, NotExported, Unknown}`; `ApiExportClosureEntryV1` (terminal
  physical index, terminal module, local symbol, declaration name, status,
  reason, root exporter index/module, chain depth); `ApiExportClosureFactsV1`
  (registry generation, entries, `unknown_reasons`, `truncated`,
  `format_version`). Flat scalars only.
- `20.hir/hir_lowering/api_export_closure_projection_v1.spl`:
  `project_api_export_closure_v1(registry, routes, signatures) ->
  ApiExportClosureFactsV1`, pure.
- `30.types/type_infer/api_exposure_closure_v1.spl`:
  `apply_api_export_closure_v1(exposure, closure) -> ApiModuleExposureV1`,
  pure. `walk_api_exposure_v1` and `project_api_export_routes_v1` are not
  edited; their specs stay collateral. `ApiCallableExposureV1` gains a
  defaulted `export_status` field (`NotCollected` until applied).
- `CompileContext.api_export_closure_facts: ApiExportClosureFactsV1?`,
  computed in `run_typecheck_warn_pass` right after the route projection and
  applied to every retained exposure row; cleared at pass entry and compile
  entry together with the route facts; kept by the retain-products path.

### Module verdict after closure

`apply_api_export_closure_v1` replaces
`effective-export-closure-not-collected` only when every retained callable of
the module has a closure entry; otherwise the reason stays and
`export-closure-incomplete` is added. The module verdict is then:

- `Violates` iff some `Exported` callable walks `Violates`;
- else `Unknown` iff any module-level unknown reason remains (budgets,
  malformed facts, binding failures), any `Exported` callable walks `Unknown`,
  or any callable's closure status is `Unknown`;
- else `Safe`. An empty exported set with no unknowns is `Safe`: the module
  publishes nothing.

`NotExported` callables never drive the module verdict; their findings are
retained for the explain path. This is a deliberate behaviour change for E2:
a leaf `export`ed callable that its facade does not re-export is no longer a
denied root, because it is not part of the effective public API
(REQ-EAPI-001). The decision counts such roots as `excluded_roots`.

### Unknown denial

With the closure collected, `decide_api_publication_v1` may deny `Unknown`
roots at a `Deny` disposition (REQ-EAPI-003 fail-closed) under the existing
explicit activation. Consequence to state, not hide: every export whose
signature carries a `Nominal` node is `Unknown("nominal-members-not-projected")`
until nominal members are projected, so active robust builds of real code are
denied for that reason. The switch therefore lands as its own commit with the
publication-guard spec's "unknown roots" case flipped RED->GREEN on purpose,
and the activation default stays an open owner question.

### Spec obligations for the code slice

`test/01_unit/compiler/hir_lowering/api_export_closure_projection_v1_spec.spl`
(RED: module missing): facade re-export is `Exported` with the facade as root
exporter; direct-only leaf export under a facade is `NotExported` naming the
facade; a module with no facade in the registry is its own root; a route with
an unknown reason propagates to `Unknown`; missing registry/routes yield no
entries and an explicit reason. `api_exposure_walker_v1_spec.spl`,
`api_export_route_projection_v1_spec.spl`, `api_signature_projection_v1_spec.spl`
stay collateral; `api_publication_guard_v1_spec.spl` gains the excluded-root
and (separately) the Unknown-denial case.

## P12 export hardening (design, 2026-11-06)

Status: design handoff, docs only. Owner answer on "hardening" is both: (a)
the fail-closed typing invariants already carried by E1/E2 (every gap is an
explicit `Unknown` reason, never `Safe`), and (b) plan P12 "Export hardening,
privacy and complete graph round-trip" (AC-TRC-052/053, REQ-TRC-031). This
section scopes (b) and ties it to (a). No report projection (P6) exists yet
in `src/app/traceability` (`structural_report_v1.spl` is the P0 lane's
structural check, not a Markdown/HTML export), so the first code slice waits
for the P6 projection seam; a pure admission module with no consumer would be
dead code and is not authored here.

### Scope

An *export* is any projection that leaves the process as a file or stream for
another reader: Markdown/HTML reports (P6), SDN graph dumps and their
round-trip import, independent edge pages (P2/P12), and the typing facets the
trace graph consumes from the compiler (T1: `api_*` facts, closure entries,
publication decisions). Terminal tables and SDN on stdout are not exports
unless written to an explicit destination. The CLI JSON adapter, when
requested, is an export and follows the same rules.

### Invariants (fail closed; each is a gate, not advice)

1. **Explicit destination.** No export without an explicit path. The path is
   canonicalized once; a symlink anywhere on it, a traversal segment, or a
   destination that resolves outside the declared output root is refused
   before any byte is written. Collision with an existing file is refused
   unless the caller declared overwrite; a failed or partial write leaves the
   previous output untouched (write to a sibling temp name, then rename).
2. **Private material never renders.** Absolute filesystem locations,
   prompts, credentials/tokens, environment values, and source text of
   non-public declarations are filtered *before* the render stage, from the
   projection record, not scrubbed from the rendered text. Paths render as
   safe repo-relative spellings or are omitted with a `redacted` marker.
3. **Untrusted content is data.** Every rendered name, message, URL or
   snippet is escaped for its target (Markdown, HTML attribute/text, SDN
   string). HTML is offline: no script, no automatic remote resource, no
   inline event handler, `javascript:`/`data:` URLs rejected. Injected markup
   in a declaration name or diagnostic must appear escaped or the export is
   refused; it never executes or links out.
4. **Deterministic and byte-identical.** The same subject at the same
   snapshot renders byte-identical output across runs and hosts: stable
   ordering, no timestamps/hostnames/pids, no locale-dependent formatting.
5. **Visibility-safe counts.** An export never reveals nodes or counts the
   reader's visibility scope excludes; totals are computed after filtering.
   Truncation is explicit (`truncated: true` plus the bound), never silent.
6. **Complete graph round-trip.** An SDN graph export re-imported yields an
   identical graph (same node/edge identity, same unknown reasons); edge
   pages are independently fetchable and together cover the edge set exactly
   once. Lossy exports must say what they dropped.
7. **Typing facets keep their reasons.** When trace consumes `api_*` facts,
   the export carries every `unknown_reasons` entry, `export_status`,
   `excluded_roots` and the decision disposition verbatim. An export may not
   collapse `Unknown` into `Safe` or drop the scope marker
   (`non-callable-and-generated-surfaces-not-collected`). This is the bridge
   to hardening (a): trace never claims more than the compiler proved.

### Gates (what the first slice must ship, and in what order)

- Design first (this section), then a pure `00.common`-level admission record
  (`ExportAdmissionV1`: destination verdict, redaction count, escaping
  verdict, truncation, reasons) consumed by the P6 projection the day it
  exists; an admission with any refused reason yields no file.
- Executable specs under `test/` only, each with a real fixture: traversal
  and symlink escape refused; collision/failed write preserves prior output;
  injected `<script>`, `javascript:` URL and Markdown link injection appear
  escaped; absolute path and prompt text never appear in output; repeated
  export is byte-identical; filtered graph counts match the visible node set;
  SDN round-trip equality; typing facet reasons preserved. No manual-only
  evidence substitutes for these.
- `check-*` push-tier rows are out of scope until the projection exists;
  until then the admission spec is the gate.

### Open questions for the owner

- Output root policy: fixed `build/` or caller-declared root with the
  refusal above? (Design assumes caller-declared root inside the worktree.)
- Whether a redaction count above zero should be a warning in the report
  header (visible honesty) or silent (privacy). Design assumes visible count,
  never the redacted values.

### AC-EAPI-005 generated-surface recheck (finding, 2026-11-06)

Rechecked against the code: `guard_api_publication_v1` runs once at phase-5
mode dispatch (`driver_orchestration.spl:394`) over facts collected by the
retained typecheck pass, i.e. **before** `weave_aop()`
(`driver_orchestration.spl:590`, AOT path after borrow check) and before
native staged codegen / postmono specialization. Generated exports that the
surface builder already sees (`generated-comment` export origins from
generated files, `module_surface_declarations.spl:191`) do reach the route
projection and the closure. Exports introduced *after* the guard by AOP
weaving or specialization are not rechecked: the AC-EAPI-005 gap is
confirmed, not closed. Closing it is feature-sized: a second evaluation of
the guard after weave over post-weave HIR facts (re-running
`collect_module_typecheck_receipt_v1` on the woven modules and re-projecting
routes/closure), with a spec whose aspect introduces a `bool`-returning
export. Recorded in the todo; no partial recheck is shipped, because a guard
that runs only before weaving must not be described as covering it.

### Implemented (2026-11-06, follow-up to the design above)

The code slice landed as designed with two refinements the seed run forced:

- **Scope marker does not block Safe.** The projector publishes
  `non-callable-and-generated-surfaces-not-collected` for every module
  unconditionally. It bounds what the verdict claims (callable surface only;
  types, constants and generated surfaces are still unobserved) and is kept in
  `unknown_reasons`, but `apply_api_export_closure_v1` does not let it block
  `Safe`. Every other module-level reason (budgets, malformed facts, binding
  failures, generic bounds, effects) still does. A `Safe` module verdict is
  therefore a *callable-surface* verdict.
- **Unresolved facade spelling is Unknown, not NotExported.** The surface
  builder creates no origin row for an `export use` it cannot resolve (seen
  with a directory alias such as `export use pkg.fixture.{hidden}` when the
  registry carries only `pkg.fixture.__init__`). The closure reads each
  facade's raw `exports` items by last dotted segment: a facade that spells
  the callable but has no route for it yields
  `Unknown("export-origin-unresolved:<facade>")`. Re-export through a middle
  facade spelled by its facade name (`export use pkg.fixture.__init__.{flag}`)
  resolves transitively to the terminal and joins; the outer facade becomes
  the root exporter at chain depth 3.

Unknown denial is active under the explicit flag at a denying profile: every
unknown root is named in the diagnostics with its reason. The spec lives at
`test/01_unit/compiler/type_infer/api_export_closure_projection_v1_spec.spl`
(beside the other E1 specs): RED (ERROR, 0 executed) -> GREEN 5/5 on the seed;
`api_publication_guard_v1_spec.spl` 7/7 -> 8/8 with the unknown-root case
intentionally flipped to deny; walker 7/7, route 7/7, signature projection
7/7 unchanged. The full `compile()` choke point remains verification-pending
on a self-hosted binary.
