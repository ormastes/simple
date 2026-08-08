# native-build: cross-function `Result` text-payload match is non-deterministic

**Severity:** high (non-deterministic silent-wrong)
**Found:** 2026-07-14, errhandling lane
**Resolved:** 2026-07-15
**Backend:** native-build `--entry`

## Symptom

When `Err("text")` is **constructed in one function** and matched
(`case Err(e):`) in a **different function**, repeated `--clean` rebuilds of the
identical source flip between correct output (`"boom"`) and a garbage i64
bit-pattern printed as text — depending on function-processing order.

## Root cause

The flat parser also collapsed every `Result<T,E>` annotation to a bare
`TYPE_RESULT`, discarding both generic arguments before HIR. Then
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`:
`lower_enum_construct_named`/`lower_enum_lit` (~L1084-1141) register
`enum_payload_struct_names["Result::Err"] = enum_text_payload_marker()` only at
the **construction** site. `lower_enum_match` (~L868-899) consumes that same
module-level dict when binding the payload at the **match** site. When the two
sites are in different functions, whether the marker is already registered
depends on non-deterministic function-processing order → the match sometimes
sees no marker and decodes the text payload as a raw i64.

## Resolution

The flat parser now preserves `Result<T,E>` through the same compact
specialization-registry pattern already used for `Dict<K,V>`. Result payload
text-ness is then derived at each match site from the scrutinee's declared
`Result<Ok, Err>` type. MIR recovers that type from a typed variable or
parameter, or from a called function's declared return type, then decodes only
the selected `Ok`/`Err` payload when its own generic argument is `text`.

The construction-site marker remains a fallback for untyped/user-enum cases,
but a known non-text Result no longer consults it. This removes function-order
nondeterminism and avoids the equally dangerous global-key mistake where a
`Result<i64,text>` construction could make `Result<i64,i64>.Err` decode as text.

`scripts/check/check-native-seed-parity.shs` covers typed-parameter and direct
call matches for cross-function text plus integer Result payloads in the same
module (`boomboom41`) in the 40-case gate.

## Reproduce

`/tmp/wt_errhandling/` probes; run the same `--entry` build 3× with `--clean`.
