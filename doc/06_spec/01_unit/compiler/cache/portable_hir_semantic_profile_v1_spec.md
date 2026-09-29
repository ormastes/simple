# Portable HIR semantic profile V1 specification

Status: inactive Slice B contract. Runtime qualification is outstanding; this
manual records executable assertions but does not claim a passing run.

Executable source:
`test/01_unit/compiler/cache/portable_hir_semantic_profile_v1_spec.spl`.

## Profile and authority boundary

`embedded-pure-closed-functions` admits only schema-2 Base/Portable concrete
function bodies with no target contract. `MacroExpansion`, `GenericBody`,
`TraitDefaultBody`, and `AroundAdvice` are typed unavailable. The HIR owner may
return copied semantic facts. It cannot issue a completeness grant: the byte
verifier availability flag is false, completeness issuance returns
`AuthorityUnavailable`, copied object references never admit, and the native
loader refuses.

No public receipt, handle, generation, pin, owner, or attempt coordinate is
accepted by Slice B. Live pin/generation/source/module/section/attempt binding
belongs to the existing C/D owners. Consequently pin loss, cancellation,
replacement, repacking, foreign-owner, restart, and stale-finish scenarios stay
mandatory for those connected owners and cannot be simulated as Slice B
successes.

## Canonical field policy

| Area | Accepted representation |
|---|---|
| Module | Nonempty name/path; function-only declaration families; no imports, target maps, types, aspects, traits, templates, constants, or other declarations. |
| Functions | Nonnegative unique ID/name; map key equals symbol; exact same-module `defining_module`; root scope; export, public bit, and visibility agree. Nonexports are Private. Parameter `SymbolId` membership is validated before the symbol table is indexed. |
| Symbols/scopes | Dense next-ID counters; unique nonempty names; builtin tag zero; exact symbol, scope, root, and module-callable indexes agree. Qualified-function/type and structural/GPU indexes are rejected as nonauthoritative profile payloads. Nonroot scopes are nonempty Function/Block scopes with valid ancestry. |
| Disabled payloads | Export, driver-manifest, VHDL, and parameter-default payloads are nil when their presence bit is false. Doc text, GPU target/order, and every disabled `FunctionAttr` payload are canonical empty/default values. |
| Effects | Empty and exactly one explicit Pure normalize to the same digest through the semantic owner. Duplicate Pure and IO/Async/Throws/Mutates/Allocates/Custom refuse. |
| Values | Exact signed i8/i16/i32/i64, bool, or unit only. Integer value and suffix must match its stored type. |
| Executable nodes | Typed literals, active immutable parameter/local variables, immutable Let, expression/block statements, valued blocks, required-else If, and direct local calls only. Every other expression/statement kind refuses, including unreachable nodes. |

## Deterministic facts and graph

The verifier walks every function and executable node, reconstructs lexical
bindings, checks stored types, return types and exact call arity/types, and
derives calls from the AST. Dependency rows are unique caller/callee edges;
call-site occurrence count is separate. Length-prefixed components make keys
injective. Sorted node/edge order plus one indexed adjacency build feeds Kahn
cycle detection and DAG longest-path propagation. Exact depth is accepted and
one-over depth returns typed `BoundsExceeded` independent of insertion order.

The executable scenarios cover repeated edges, component-boundary names,
permutations, diamonds, disconnected functions, self-cycles, mutual cycles,
and exact/over-depth chains. Exported facts bind symbol ID, name, parameter and
return types, normalized effect digest, graph digest, and profile/rules identity.

## Shared resource ledger

One ledger can cover multiple bodies. It separately counts body objects,
functions, symbols, scopes, exports, parameters, semantic nodes, unique edges,
dependency-graph nodes, call occurrences, semantic traversal depth, text bytes,
encoded bytes, retained bytes, and work units.
Limit construction rejects values outside fixed ceilings; checked charges occur
before count-derived sorting/traversal/retention. Graph indexes, sorting,
descriptor copies, and header work are conservatively charged. Exceeding a
valid limit returns `BoundsExceeded`, not `UnsupportedSemantics`.

Semantic-fact construction computes the exact canonical transitive-effect text
size from validated function IDs/names and reserves its text budget plus the
export-descriptor/dependency-copy retained budget before allocating the effect
rows, entry index, joined effect text, or copied entry array. Exact two-body
aggregate budgets admit both bodies; a text or retained limit one byte below
that aggregate refuses the second body through the corresponding typed budget.
Every parent transition in symbol/scope validation and function-owner lookup
also consumes one work unit, so deeper valid scope ancestry cannot evade the
shared work ceiling.

Encoded-byte charging remains dormant while the byte-verifier bridge is closed;
the bounded codec owns decode/re-encode accounting. The test contract includes
a canonical bounded-decode versus direct-typed fact-equivalence scenario for
execution after Slice A and an admitted self-hosted runtime are available.

## Executable scenarios

1. Keep byte/completeness authority closed and unsupported body kinds false.
2. Derive identical exact facts from repeated typed Base fixtures.
3. Compare direct facts with facts after canonical bounded codec decoding.
4. Reject defining-module, scope, builtin, visibility, exact/qualified/module index, and sibling-scope substitutions.
5. Reject duplicate exports/names, wrong function keys, and extra declarations.
6. Reject disabled export/driver/VHDL/default payloads, target/doc data, and unreachable unsupported nodes.
7. Normalize Pure through the semantic owner and reject every forbidden effect family.
8. Reject wrong stored return type and wrong direct-call arity.
9. Reject a parameter whose `SymbolId` is absent without indexing the missing row.
10. Check signed-width minimum/maximum/one-below/one-above and suffix rules.
11. Deduplicate edges and prove framing/permutation stability.
12. Check diamond/disconnected DAGs, cycles, and exact/over call-chain depth.
13. Check typed limits plus aggregate two-body ledger refusal.
14. Admit exact two-body effect/descriptor budgets and reject text/retained limits one byte below exact.
15. Charge every scope ancestry hop, admit its exact work budget, and reject one unit below exact.
16. Refuse copied references and every legacy byte/native admission path.

Frozen helper names required by later integration manuals are
`given_real_encoded_hir_body` and `then_exact_dependency_edges`. Scope sealing,
allocation observation, and fourth-payload denial helpers remain in their
respective owner slices; no mock-success replacement is present here.

## Evidence status

No qualifying runtime receipt exists. TDD retained a pre-production focused RED,
then the post-edit command
`bin/simple test test/01_unit/compiler/cache/portable_hir_semantic_profile_v1_spec.spl --mode=interpreter --fail-fast`
returned rc 1 with 16 executed, 6 passed, and 10 failed. Every scenario entering
semantic-fact construction reported the shared interpreter diagnostic
`type mismatch: comparing string with integer`; therefore the new missing-ID,
aggregate-budget, and scope-hop assertions did not execute and are not claimed
as passing evidence. The selected `bin/simple` also identified itself as a
Rust-built bootstrap seed, so both observations are diagnostic/nonqualifying.

Compiler/lib/MCP, native/profile-matrix, diagnostics-equivalence, allocation,
and performance evidence must be collected once on an admitted self-hosted
runtime and reviewed independently before either availability flag can change.
