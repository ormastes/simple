# Collection planner identity maintenance

Treat builtin dispatch identity separately from user SymbolIds. Array
operations must not acquire a fabricated instance-method symbol or become
trusted solely through method spelling on an arbitrary receiver.

The in-progress candidate appends a bounded BuiltinCollection identity to
MethodResolution. Preserve earlier enum tag indices; generate the HIR codec
with `src/app/compiler_schema/main.spl codec`, and update both ordinary and
canonical codec versions when changing the schema. Audit resolver transport,
provider relocation, effect/type inference, SFFI identity, and backend
consumers for exhaustive matches.

Preserve existing instance/trait/UFCS precedence. Dispatch shape does not
prove callback effects, output types, aliasing, order, or rewrite legality.
Retain original untyped bootstrap behavior and reject malformed canonical
identity at the consuming backend boundary.

Current blockers: item 3 integration spec has an unimported MIR serializer
and an unresolved filter interpreter result mismatch; the quiet resolver is
still opt-in. Production registry, typed extraction, physical planning,
cross-engine execution, and performance certification remain unfinished.
Do not advertise this candidate as complete or production verified.

Superseded 2026-10-25: profile-switchable containers (seven-plan item 7) are
tracked in `doc/04_architecture/compiler/profile_switchable_container_algorithms.md`
§ Status reconciliation (2026-10-25). Only the literal-membership MIR consumer
landed (`97b13f9eb09`, `bb7d5313b2f`); general typed lowering and two-run
host execution evidence remain OPEN.

Superseded 2026-10-25: the BuiltinCollection identity is no longer only an
in-progress candidate — it is present in `hir_types.spl`, the generated HIR
codec and type inference on release/1.0.0. MIR now consumes guarded
literal-membership plans (`97b13f9eb09`); general lowering, cross-engine
execution and NFR certification remain unfinished. Re-verify the
"integration spec" blockers above before quoting them; they were not
re-run on 2026-10-25.

Added 2026-11-06 (adaptive collections C1): semantic contracts, operation IDs,
creation origins and the accounting oracle live in
`src/compiler/35.semantics/perf_facts/collection_contracts.spl`, with the spec
`test/01_unit/compiler/semantics/collection_origin_identity_spec.spl`. These records
describe meaning only and authorize no rewrite.
- Operation IDs are keyed by canonical type identity plus method. Maintenance
  methods such as `Map.rehash` stay unmapped on purpose.
- `CollectionOriginV1` keeps the exact `ast://` feedback site ID, so existing
  `.sprof` feedback still binds. It adds a token fingerprint that ignores
  whitespace and comments, and both are built from
  `parser_collection_site_stem` in `collection_feedback.spl`. Do not build a
  second site formula.
- Remapping rejects ambiguous candidates instead of guessing.
- Trap: on the Rust seed most `adaptive_*` lib specs fail because the
  interpreter has no `spl_collection_capture_*` or `spl_ordered_key_cmp`
  externs. Compare against a baseline; do not read those failures as a
  regression. Census:
  `doc/03_plan/compiler/data/adaptive_collections_c0_census_2026-11-06.md`.

Added 2026-11-06 (owner decision, C2 site part): collection site IDs use a
versioned `#n1.<fnv>` hash of the normalized declaration, with comments and
insignificant whitespace removed. The pure-Simple
`parser_collection_normalize_declaration` and the seed's
`normalize_collection_declaration` (`parser_impl/attributes.rs`) are twins.
Both parser tests pin the same values (`hot#n1.3808762660471155820`,
`values#n1.5053061337019949519`), so change both together or neither.
`@collection_algorithm("algo", "a.label")` replaces the hash with
`ast://<module>/label/<label>`; labels are unique per module, and a
duplicate is a parse error. Profiles recorded with the old byte-hash IDs no
longer bind; the owner accepted that. Spec:
`test/01_unit/compiler/frontend/collection_site_attribute_spec.spl`.
Wiring the label to `ResolvedCollectionPolicyV1` waits for W1 (#7220).

Added 2026-11-06 (data plan W4a): the one collection policy adapter is
`src/compiler/35.semantics/perf/collection_policy_adapter.spl`. It sits above
both `ResolvedCollectionPolicyV1` and the adaptive containers; the containers
must never import the policy layer. `collection_policy_decide_v1(policy,
profile)` returns a decision in the `CollectionPlanDecision` explain shape
(selected plus one reason per candidate) or an `Err` for a pin the container
cannot honour (COL-07: no panic). `auto` returns `selected=Original,
applied=false` and the apply helpers then do nothing (COL-08). Trap:
`set_attribute(Auto)` is not a no-op; it demotes small containers, so never
route `auto` through it. Admitted switch modes are `report_only`,
`next_instance` and `exclusive_live`; the rest are errors. `report_only`
explains an ineligible pin instead of failing. The apply helpers return
`Result`: they re-check the container's own profile, refuse to rebuild a
populated container under `next_instance` (existing instances keep their
storage, plan 11.1), and refuse an ordered pin when a held map key has no
native order. Decision: `auto` over a policy that forbids a representation the
live container could switch into is an error (pin instead). Open: nothing in
production calls the adapter yet; `@collection_algorithm` still reaches the
containers through `attributed_at_site`. Wiring the policy into construction
is W6/C5 work. Spec:
`test/01_unit/lib/collections/adaptive_policy_adapter_spec.spl` (on the seed,
the populated-map `it`s need `spl_ordered_key_cmp`).

Added 2026-11-06 (data plan W4b): `frozen_lookup()` on `AdaptiveTextSet`,
`AdaptiveMap` and `AdaptiveSet` returns a view type
(`AdaptiveTextSetFrozenLookup`, `AdaptiveMapFrozenLookup`,
`AdaptiveSetFrozenLookup`) with only `fn` methods, so a holder cannot promote,
migrate or bump counters (COL-09). The ordinary `contains`/`get` still promote
in place for the exclusive owner. Frozen reads are not profile-captured. The
map view answers an ordered-storage probe without native order as absent
instead of demoting. The text-set view holds the class reference (live reads);
the map/set views hold a value copy (a snapshot). Seed: the text-set COL-02,
COL-04 and COL-09 scenarios run; the populated-map ones need
`spl_ordered_key_cmp`.
Owner question (W4b): frozen reads are not captured, so a site read mostly
through views reports few lookups and `auto` feedback never promotes its next
instances. Capturing them needs the lockless capture runtime (adaptive lane).
