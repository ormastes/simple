# Source union admission and independent symbol ownership

Executable specification: `test/01_unit/compiler/verify/source_union_admission_v1_spec.spl`.
Requirement: REQ-C2-UNION-TRANSPORT-001. All twenty-three scenarios are **UNRUN**.

The real APIs under test are `SourceUnionLedgerV1.create`, `debit`, `enter`,
`snapshot`, `source_union_clone_symbols_v1`, and `source_union_preflight_v1`.
The preflight scenarios use the actual target-aware parser and HIR lowerer.
No synthetic success flag stands in for normalization or source export.

| Scenario | Assertion |
| --- | --- |
| Invalid limits | Negative or increased ceilings refuse before traversal. |
| Exact debit | Exactly two allowed nodes succeed; a third refuses without advancing usage. |
| Count evidence | Negative counts and unknown counter names refuse without advancing work. |
| All growth categories | Every actual debit category accepts its exact ceiling, refuses one more with its own code, preserves span and exposes copied counters. |
| Depth | Exact depth succeeds; deeper traversal refuses with the last admitted depth. |
| Fresh owner | Changes to returned scope dictionaries, every string index, GPU indexes, registry maps and both ID counters leave the input unchanged. |
| Root mirror | Conflicting input root views refuse without repairing either view. |
| Late clone boundary | Actual clone succeeds at its measured copy allowance; one less refuses during reverse-owner copy and leaves registry, root scopes and counters unchanged. |
| Copy budget | A zero copy allowance refuses before constructing an owner. |
| Parsed signatures/defaults | Actual union parameter/result/default metadata is visited without registry or key growth. |
| Union-free traversal | Actual node debit succeeds at the exact limit and refuses at one less. |
| Unsupported nesting | A union under an outer Optional refuses before key or registry allocation. |

The ledger reports deterministic logical debits, not measured RSS. Parser and
HIR-lowering limits remain separate. The preflight visitor is read-only; it
covers current HIR expression, statement, pattern, type, declaration, default,
contract, symbol-type and dimension children. Opaque custom/assembly/hardware
or frontend extension payloads are not rewritten: when a module contains a
union they produce a position refusal. No native execution, proof result,
performance qualification, or Phase3 completion is claimed.

Physical backing-capacity work is an unresolved borrowed-API limitation:
`Dict.len()` admits logical rows and is checked against `keys().len()` after
snapshot creation, but does not expose or bound hidden native dictionary
capacity/tombstones. These tests must not be cited as a physical iteration,
allocation, latency or RSS bound for `Dict.keys()` or dictionary insertion.

## Revision2 review repairs

Frozen revision1 and review cycle1 are preserved. The revision addresses
C2-ADM-R1/R2/R3 without adding runtime or physical-work qualification:

- Required module, declaration key/row, scope/symbol identity, function,
  statement, pattern, parameter and dimension records are checked before
  their first field access. Genuine parsed extern/required-trait controls
  exercise permitted absent bodies; an ordinary absent body is refused.
- Every retained typed payload behind a false presence flag is visited and
  charged. Hidden unions refuse `UNION-E-PRESENCE`; retained ordinary scalar
  trees consume the same node/work/depth allowances. Valid NilLit/Unit/Infer
  placeholders remain permitted. A true presence flag requires its payload.
- Nullable metadata text is preserved without calling native length on nil.
  Required identity strings remain distinct from nullable metadata. The
  multibyte text control charges six UTF-8 bytes for `é🙂`. Nil array fields
  use the existing empty-array representation without blanket rejection.
- The clone oracle asserts both changed clone values and unchanged originals
  across all fourteen fields, including nested scope maps and a resolved type
  payload. Snapshot isolation now includes a successful subsequent work debit.

Eleven added scenarios cover nil module/current scope/rows, malformed declaration
keys/rows, absent function bodies and kinds, real extern/trait declarations,
inactive union annotations/results/defaults, deep inactive scalar trees,
nil/empty/multibyte text and nil arrays, and absent parameter/pattern/dimension
children. All twenty-three scenarios remain **UNRUN**.
