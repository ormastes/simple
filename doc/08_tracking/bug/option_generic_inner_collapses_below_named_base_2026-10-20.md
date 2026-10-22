# `Option<T>` loses T for every structured, non-callable inner type

- id: option_generic_inner_collapses_below_named_base_2026_10_20
- status: open
- found: 2026-10-20, while writing the prevention spec for PR #3914
  (native_optional_fn_payload_binding_arity_mir_2026_10_20)
- owner: frontend (flat type parser)

## Defect
`parser_parse_type_impl` (`src/compiler/10.frontend/core/parser.spl`, `type_name == "Option"`
branch) registers an `Option<T>` inner tag only when
`inner_type >= TYPE_NAMED_BASE or is_function_tag(inner_type)`. Every other structured tag is
interned below `TYPE_NAMED_BASE` (10000): Dict 1000, Result 2000, Tuple 3000, array 4000,
reference 7000, pointer 8000 (`src/compiler/10.frontend/core/types.spl`). Those fall through to
bare `TYPE_OPTION`, which the bridge turns into an argless `Option` and HIR lowers to
`Optional(Any)` (`20.hir/hir_lowering/types.spl`, `name == "Option"`). The postfix spelling
`(fn(..) -> R)?` takes the named-type postfix branch and loses the callable the same way.

## Evidence (producer8, `compile --format=smf`, 2026-10-20)
- `Option<[i64]>` field, `if val xs = h.xs: for x in xs` and parameter form -> `for-in over
  non-array iterables is not supported by native codegen yet (#143) (collection mir type: Tuple`;
  `h.xs.unwrap()` then `for` -> same, `collection mir type: I64`.
- `(fn(text) -> i64)?` field, `if val f = h.cb: f("x")` -> `dynamic callable requires proven arity
  before indirect emission`.
- Pass: `[i64]?`, `Option<fn(text) -> i64>`, `Option<Dict<text, i64>>` (`.len()` is dynamic on Any),
  `Option<(i64, i64)>` (`.0` is dynamic on Any).
- Fixtures: `C:/dev/simple-bootstrap-storage/hir-specs-fx/src/app/hx/i*.spl`, runner `run.sh`.

## Fix direction
Register the inner tag for every non-primitive inner (drop the `>= TYPE_NAMED_BASE` gate, keep
the dedicated I64/F64/TEXT/BOOL tags), and route `(<type>)?` through the same registration.

## Specs
- Prevention (in-development): `test/01_unit/compiler/20.hir/bootstrap_regressions/option_generic_inner_type_gaps_spec.spl`.
- Passing sibling (#3914 reproducer + working shapes): `test/01_unit/compiler/20.hir/bootstrap_regressions/option_generic_inner_type_spec.spl`.
