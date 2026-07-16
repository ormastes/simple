# Bootstrap generic `Dict` dedent state leak

## Status

Open. A pure-Simple bootstrap entry-closure parse repeatedly leaves the next
top-level declaration inside the preceding struct/class/enum after parsing a
raw `Dict<K, V>` annotation. Named `{K: V}` aliases avoid the failure, but are
only containment; the parser/runtime root cause remains.

## Current evidence

The same preserved-cache 428-file build advanced one boundary per focused
alias correction:

- `build/mini_builds/bootstrap_main_sdn_alias_cycle1.log` cleared the SDN
  optional-return failure and stopped at `async_integration.spl:188`, after
  `AsyncStateMachine.locals_snapshot: Dict<i64, MirOperand>`.
- `build/mini_builds/bootstrap_main_async_alias_cycle2.log` cleared that site
  and stopped at `borrow_check/nll.spl:144`, after
  `LivenessResult.live_out: Dict<i64, [i64]>`.
- `build/mini_builds/bootstrap_main_nll_alias_cycle3.log` cleared NLL, parsed
  117 files, and stopped at `backend/objects.spl:27`, after
  `ObjectRecord.fields: Dict<text, Value>`.

All failures occur in parse phase before object emission. The focused source
checks pass after each named-map correction, and
`generic_dict_struct_adjacency_spec.spl` passes six examples.

## Root-fix investigation

Inspect the interaction between:

- `parser_parse_type_impl`'s early generic return and optional-suffix handling;
- `dict_type_register` and its bootstrap-interpreted array state;
- lexer indentation/dedent state immediately after `Dict<...>` annotations.

Do not continue converting every production field to an alias. A read-only
scan found many later raw generic fields, so that approach does not converge.

## Acceptance criteria

1. A behavioral parser regression parses raw `Dict<K, V>` fields followed by
   top-level `struct`, `class`, `impl`, and function declarations without
   diagnostics or ownership leakage.
2. `Dict<K, V>?` return types absorb the optional suffix and preserve the next
   enum method/declaration boundary.
3. The pure-Simple bootstrap entry closure parses all 428 files without a
   generic-map boundary failure.
4. Existing generic key/value specialization reaches the flat AST/HIR intact.
5. Replace or explicitly retain containment aliases only after the root fix is
   proven; do not use new aliases as substitute completion evidence.
