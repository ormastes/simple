# Typed class-owner iterator acceptance

Status: UNRUN. Authored review companion; canonical spipe-docgen has not run.

Executable: `test/01_unit/compiler/semantics/iterator_class_alias_acceptance_spec.spl`

Executable SHA-256: `13596363d05c1a3fef8125e217a387aa47a608570c95106219cb20d653701cea`.

Each scenario parses actual source with an explicit filename, lowers to HIR, requires no lowering diagnostics, and validates the real Bag field declaration identity/type before calling production SafetyChecker. The actual checker owner-field index must retain that exact declaration SymbolId. No local alias checker exists in the spec.

| Program | Expected E1048 | Mutation position |
|---|---:|---|
| Class-owner alias mutates active items | 1 | 8:9 |
| Alias of class parameter mutates active items | 1 | 7:9 |
| Separately constructed owner mutates its own items | 0 | — |
| Array value copy mutated while original iterates | 0 | — |
| Shadowed alias denotes a fresh owner | 0 | — |
| Alias rebound to a fresh owner before iteration | 0 | — |
| Owner rebound during iteration; original alias mutates | 1 | 10:9 |
| Branch may select active owner | 1 | 13:9 |
| Both branches select other known fresh owners | 0 | — |
| Alias mutation after iteration | 0 | — |

The array value-copy control additionally invokes actual MirLowering.prescan_module_struct_names and lower_module, requires no MIR diagnostics and exactly one arrcopy_cond block for the live copied source. This proves the producer path only once executed; source authorship is not evidence of a runtime copy.

The original eleven direct SymbolId scenarios remain separate and byte-identical. Existing checker invocation, unsafe handling, profiles, and known mutator names are retained. No generic unknown-call rejection is added. Exact source filename propagation remains unqualified.

Coverage limits: no general nested projections, copied-struct array independence, imported class identity, dynamic-index identity, unknown explicit references, unknown external effects, cross-parameter disjointness or loop-carried fixed point. The production context records unsupported place sites; no whole G7 safety PASS is claimed.

## C2 unsupported-transfer boundary regressions

Four appended scenarios use actual parsed While, Loop, MatchCase and For programs that assign an outer class alias, then mutate through that alias while a different known owner is iterated. C1's sequential/single-iteration transfer would wrongly retain the last visited owner and diagnose it as exact. C2 requires zero such stale-identity diagnostics and exactly one unsupported-boundary ledger entry at the supplied source file's line 8, column 5. This checks analysis-boundary honesty; an empty diagnostics array here does not prove iterator safety for the unsupported transfer.

The original ten scenario bodies and production MIR array-copy oracle are preserved byte-for-byte. Existing exact-one alias rejection scenarios also guard the single-owner E1048 hook repair. Original direct eleven remain unchanged. Execution and docgen remain UNRUN; no observed RED/PASS is claimed.
