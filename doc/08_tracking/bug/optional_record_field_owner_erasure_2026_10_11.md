# Optional record field owner erasure before text slice

Status: OPEN — P1 compiler defect. Tagged application workaround only.

## Actual failure

Producer `892b220e19b5cbafd620190c95b9a2f26fc5ebc08304b8b07d4475da0ea7abb0`, source
`b58baa89e4d65a40768fceaf8221fdbdbe58da24`, PostgreSQL Phase4 collection completed
71 HIR modules and exited 1 in MIR. The seven distinct `unresolved method call: slice`
sites are `row_value_helpers.spl:703:15,711:18,713:20,731:15,736:18,738:20,774:15`;
they were printed twice each. This group is separate from the other PostgreSQL failures.
The retained terminal receipt and log are under
`/mnt/c/Temp/simple-phase2-cuda-owner-20261011/b58-phase4-essential-collection-v1/postgres/build/`.
The source diagnosis is `postgres-optional-record-field-source-diagnosis.json` in that
artifact base. No actual cached HIR payload was decoded to prove the exact dispatch branch.

## Contract and source cause

`SqlExpr.right` is `SqlExpr?`; its payload's `value` field is text. The original helpers
check presence then alias the Optional without binding its payload, and read
`expr.right.value`. Current release3bb retains this syntax. Direct Named field ownership
is registered and rebound, but Optional Named field metadata can retain provider-local
IDs without a qualified payload owner. Field resolution then loses the text receiver.
The implicit field/nil contract is not being redefined by this workaround.

Existing `optional_bound_struct_scalar_field_spec.spl` and the imported
`native_optional_payload_field` fixture establish explicit `if val` extraction as the
available contract. MIR lowers it through `rt_is_some`, a present-edge payload extraction,
and the existing nil sentinel on the absent edge. This change uses that language form;
it does not mark the Optional wrapper as a record or introduce an unconditional unwrap.

## Scoped workaround

Only `_like_prefix_str`, `_like_any_prefix`, and `_extract_like_pattern` replace their
guards plus unextracted aliases with nested `if val` bindings. Each helper carries an
`@workaround` tag. The final empty-string default, quote condition/slice, wildcard loop,
byte counter, early returns and matching choices are unchanged. No compiler maps,
visibility changes, public API additions, numeric parser changes, or host calls are added.
The first two helpers still return empty when there is no wildcard; the third returns
the complete unquoted pattern. The seven original expressions remain in the reproduction.

## Reproduction and prevention

- `test/fixtures/compiler/optional_record_field_owner_original/main.spl` contains all
  three original helper bodies byte-for-byte from release3bb, including all seven slice
  expressions. It asserts nil/no-right defaults, quoted and unquoted strings, percent,
  underscore, no-wildcard behavior and UTF-8 prefixes. It is an OPEN compiler reproduction,
  not a passing workaround fixture. Expected acceptance after a real compiler repair is
  successful MIR/object/link/run and exit 0; no fixed diagnostic count is assumed for
  this smaller module.
- `test/01_unit/lib/database/pure_database_optional_like_binding_spec.spl` exercises the
  production helpers through public in-memory SQL. Six cases assert actual row IDs and
  counts for absent WHERE, empty pattern, quotes, percent, underscore, leading wildcard,
  no wildcard and UTF-8. Private helper imports and copied implementation tests are avoided.
  The public absent-WHERE control does not claim direct helper nil-edge execution; direct
  nil/no-right assertions are retained in the original reproduction.

## Admission still required

All new tests are AUTHORED_UNEXECUTED. No compiler/native run, recovered object, or successful
PostgreSQL build is claimed. A qualified new producer must compile the actual failed
PostgreSQL closure with these three helper changes, establish that the original seven
slice failures are gone and preserve all remaining diagnostics. If other groups still
prevent an object, report that boundary; do not call the application working. Then run
the six compiled public SQL cases with zero failures/skips and separately collect the
unchanged original syntax reproduction. Full compiler/lib/MCP/LSP semantic and stdio
gates remain required before release. Keep this bug OPEN until the original syntax,
provider collisions, explicit extraction, nil behavior and native values are qualified.
