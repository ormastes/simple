# Recursive Lean declarations — authored executable specification manual

Source: `test/03_system/compiler/lean_recursive_declarations_spec.spl`.
Fifteen scenarios, actual public backend APIs. Runner, docgen, generated Lean
elaboration, kernel checking and performance measurement: **UNRUN**.
This manual is authored from the executable contracts, not generated-run evidence.

The initial twelve scenarios were frozen before implementation in the external
`tests-first` packet. Positive recursive assertions were source-predicted RED
against af10a7a because the prior planner refuses every cycle; no RED run occurred.
The thirteenth auxiliary-name scenario was added before its corresponding guard.
Independent cycle1 review found missing automatic SizeOf auxiliary reservations.
Revision2's two SizeOf scenarios were frozen before their guard correction;
the negative controls were source-predicted RED against revision1, never executed.

## Export positive recursive declarations

Construct actual MIR definitions, then invoke the plugin and compiler-owned
backends at Contracts level. Each positive helper calls both `export_module`
and `export_generated_module`, checking the actual returned Lean text.

| Scenario | Observable contract | Requirement |
|---|---|---|
| Self-recursive enum | One mutual block, exact qualified payload/result, tags, no axioms/sorry | REC-001/002/005 |
| Direct self-recursive struct | Inductive `mk` and explicit named projection after `end` | REC-001/002 |
| Mutual struct/enum plus function | Same group, real MIR construction and projection use exact qualified APIs | REC-001/002 |
| Same-short-name mutual enums | Cross references and metadata retain both full names and symbols | REC-002 |
| Slice/tuple/result nesting | Actual mapped Array/Prod/Except type text retains positive recursive references | REC-003 |
| Group dependency ordering | Dependency, mutual group, user order; insertion-independent output; complete flattened view | REC-004 |
| Acyclic regression | Exact complete builder text and prior lexical ready selection | REC-004 |

The mutual body scenario takes an existing recursive enum argument, constructs
the containing struct and projects the argument back. It does not invent a
constructor inhabitant for a direct cycle without a base constructor.

## Refuse malformed or unadmitted inputs atomically

Each refusal calls full/generated exports on both owners, checks the diagnostic,
then calls both `export_types` methods with builders containing `retained`.
Both builders must remain exactly unchanged.

| Scenario | Observable refusal | Requirement |
|---|---|---|
| Recursive fixed arrays | Vector beneath Result refuses; independent scalar Vector in recursive struct remains supported | REC-003/004 |
| Negative function position | FuncPtr taking the recursive type retains faithful-representation refusal | REC-004 |
| Missing/wrong nominal kind | Exact missing-symbol and kind-mismatch diagnostics | REC-004 |
| Malformed identity/members | Wrong key, duplicate type name, generated member, injected name | REC-002/004 |
| Union alongside recursion | Existing union refusal is preserved | REC-004 |
| Numbered nested auxiliaries | `rec_1`, `below_1`, `brecOn_1` are rejected before grouped emission | REC-004 |
| SizeOf auxiliary families | `_sizeOf_N`, `_sizeOf_N_eq`, `_sizeOf_inst` refuse for recursive fields and variants | REC-004 |
| Nearby valid SizeOf-like names | Nonnumeric and differently suffixed field/variant names still export through all four APIs | REC-001/004 |

Requirement shorthand `REC-NNN` means `REQ-C2-REC-NNN` in
`doc/05_design/lean_recursive_declarations.md`, derived from selected C2.

## Remaining acceptance

No PASS, coverage percentage or runtime claim follows from this file. Actual
generated modules must be elaborated and kernel checked on the exact source,
including nested wrappers and constructor/projection terms. Recursive fixed
arrays remain a named open requirement. Union semantics, general CFG, mutation,
enum elimination, calls, native layout and full C1–C7 refinement/trust closure
remain open outside this source packet.
