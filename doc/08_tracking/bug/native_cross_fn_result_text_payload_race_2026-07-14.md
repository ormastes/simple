# native-build: cross-function `Result` text-payload match is non-deterministic

**Severity:** high (non-deterministic silent-wrong)
**Found:** 2026-07-14, errhandling lane
**Backend:** native-build `--entry`

## Symptom

When `Err("text")` is **constructed in one function** and matched
(`case Err(e):`) in a **different function**, repeated `--clean` rebuilds of the
identical source flip between correct output (`"boom"`) and a garbage i64
bit-pattern printed as text — depending on function-processing order.

## Root cause

`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`:
`lower_enum_construct_named`/`lower_enum_lit` (~L1084-1141) register
`enum_payload_struct_names["Result::Err"] = enum_text_payload_marker()` only at
the **construction** site. `lower_enum_match` (~L868-899) consumes that same
module-level dict when binding the payload at the **match** site. When the two
sites are in different functions, whether the marker is already registered
depends on non-deterministic function-processing order → the match sometimes
sees no marker and decodes the text payload as a raw i64.

## Fix direction

Do not rely on module-global registration order. Derive the payload's
text-ness from the enum variant's declared payload **type** at the match site
(available from the enum decl), independent of whether a construction site was
lowered first. Same class of latent bug for any text-payload enum matched
across function boundaries.

## Reproduce

`/tmp/wt_errhandling/` probes; run the same `--entry` build 3× with `--clean`.
