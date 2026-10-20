# Positional `{K: V}` enum payload is read as a named field

- id: positional_brace_dict_payload_parsed_as_struct_field_2026_10_20
- status: open (workaround active)
- found: 2026-10-20, phase-3 MIR residue (enum_payload cluster), producer6 1622d7c0c7a

## Failure
`enum E: IndexMap({text: i64})` registers ONE payload slot of type `i64`
(the brace is taken as a named field `text: i64`), not `Dict<text, i64>`.
Constructing `E.IndexMap(self.field_package_dep_memo)` with a `{text: i64}`
value then fails MIR lowering: `enum construction 'E.IndexMap': payload type
mismatch at 0`. Reproduced on a single-module fixture with the
SIMPLE_ENUM_PAYLOAD_TRACE=1 receipt `expected='i64' remembered='dict'`;
spelling the payload `Dict<text, i64>` makes the same fixture pass.

Affected source: `src/compiler/20.hir/hir_lowering/phase_memo_ownership.spl`
(HirPhaseMemoRoot IndexMap/TextMap/IndexLists/TextLists/FlagMap), constructed
from `src/compiler/20.hir/hir_lowering/types.spl:915`.

## Workaround
`@workaround bug=positional_brace_dict_payload_parsed_as_struct_field_2026_10_20`
on HirPhaseMemoRoot: payloads spelled `Dict<K, V>`. Workaround commit: branch
`work/p6-mir-enum` (PR against release_phase3).

## Root fix (owner: frontend/parser)
A positional variant payload list must parse `{K: V}` as a dict TYPE; only a
`V(name: T)` / `V { ... }` form declares named fields. Prevention test: an
enum with a `{text: i64}` positional payload registers one `Dict(Str, Int)` slot.
Fixture: C:/dev/simple-bootstrap-storage/fix-p6enum (y_dict_field).

## Specs (2026-10-20)
- Reproducer (in-development): `test/01_unit/compiler/20.hir/bootstrap_regressions/positional_payload_brace_dict_spec.spl`.
- Prevention (passing spellings): `test/01_unit/compiler/20.hir/bootstrap_regressions/positional_payload_spelling_spec.spl`.
- Same class, found while probing neighbours with producer8 (`compile --format=smf`): a positional
  tuple payload `T((i64, text))` fails to parse (`expected enum variant name, got )`) and a
  function-typed payload `F(fn(i64) -> i64)` fails to parse (`expected enum variant name, got ->`).
  `Dict<text, i64>`, `[i64]`, `i64?` and the named form build. Both gaps are in the reproducer spec.
