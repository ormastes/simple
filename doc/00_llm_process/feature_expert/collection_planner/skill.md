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
