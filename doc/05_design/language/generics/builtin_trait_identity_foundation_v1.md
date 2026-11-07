# Canonical builtin trait declaration foundation

Status: AUTHORED / NOT_RUN. Selected full builtin matrix scope B; concrete type
support and public method policy are separate decisions. This foundation does
not activate new builtin bound enforcement in HM or lowering.

`builtin_trait_declarations_v1.spl` allocates an actual Module symbol named
`<simple:builtin-traits:v1>` and a private module scope. Clone, Copy, Debug,
Default, Drop, Eq and Ord receive actual SymbolTable-allocated Trait symbols
with internal `<builtin:Name>` spellings. Both owner and trait spellings are
unlexable source identifiers. Private scope alone is insufficient because the
canonical table has a global exact-name index. No bare lexical aliases are
installed, so declared/imported `Ord` and `Clone` retain ordinary lookup
priority, including declarations created after this registry.

Creation returns a table and registry together. It clones all table dictionaries
and each scope's binding dictionary before allocation, preserving the copied
root binding mirror. Original type/declaration payloads are read-only; allocation
does not mutate their nested type graphs. All allocator counters are copied.
Preexisting reserved spellings, malformed allocator state, wrong row kind,
wrong owner/scope, duplicate/missing entries and stale IDs are rejected. No
owner or trait row may be public, mutable, generically parameterized or carry
a builtin-method tag. Private visibility and the independent `is_public` flag
are both checked. Solver installation additionally requires complete owner
and trait row equality with its retained symbol table, including source spans.
No
arbitrary string or historical integer ID 1–7 establishes builtin identity.
Failure leaves the caller table and scope untouched.

The registry binds typed builtin kinds to local SymbolIds. Validation checks
the complete seven-row registry against its actual table, including the owner
Module binding, private scope parent, each Trait identity and private binding.
Cross-module rebinding requires both validated owner records and maps the typed
kind to the consumer's independently allocated row. Raw numeric IDs are never
copied between module-local spaces. Stable qualified identity is provided by
the existing `trait_reverse_symbol_identity_v1` function. Serialized transport
and HIR/cache provenance integration remain future consuming work; free text
deserialization is not accepted by this in-process API.

Installation requires a TraitSolver with matching symbol ownership. It first
validates every row, duplicate/collision constraints and both supertrait edges,
then calls the ordinary `add_trait` path only after all fallible validation is
finished. Copy references the registry's actual Clone row and Ord its actual
Eq row. No method signatures, primitive impl rows, special satisfaction
algorithm, or dispatch behavior are added. Existing obligation solving checks
the supertrait edges; tests use an explicitly constructed record impl as a
controlled solver fixture, not as builtin type-policy authority.

Remaining integration: ordinary name resolution first, explicit registry
fallback only on a miss; retained local/imported generic bounds; transactional
HM registration/recollection; cache identity transport; user-approved support
matrix and public Ordering representation; real compiler positive/negative
execution. Legacy `create_builtin_traits` is unchanged and is not made
canonical by this addition.

Tests: `test/01_unit/compiler/traits/builtin_trait_declarations_v1_spec.spl`.
All are authored and NOT_RUN pending an admitted full CLI. No startup, latency,
RSS, cache, or release qualification is claimed.

Allocator boundary admission simulates exactly eight canonical symbol
allocations, including structural-union reserved-ID skips, and one scope
allocation before copying. It refuses signed-counter exhaustion and validates
the resulting counter values and nonnegative in-range owner/trait/scope IDs.
The final complete i64 allocation window is covered separately from refusal
controls; all failure controls assert the original table remains unchanged.
