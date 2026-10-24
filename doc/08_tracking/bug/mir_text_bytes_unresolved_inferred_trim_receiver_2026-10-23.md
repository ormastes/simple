# MIR: text `.bytes()` unresolved when receiver type is inferred from `trim()`

Status: open (compiler fix applied, unverified by a rebuilt compiler; workaround active)

## Symptom
Stage 2 pure-Simple `native-build` of the standalone test runner fails in MIR on 1/287 modules:
`MIR lowering error: unresolved method call: bytes at src/lib/common/sdn/parser.spl:67:21`
(`val bytes = trimmed.bytes()` where `val trimmed = source.trim()`).

## Repro (stage2ref, build/repro/bytes_trim.spl)
`val trimmed = source.trim()` then `trimmed.bytes()` -> fails with the error above.
Passes MIR: `val trimmed: text = source.trim()` (v_typed) and `val trimmed = source` (v_param).
Note `val tt: text = trimmed` (copy of the inferred local) still FAILS: the inferred local's type
poisons the copy. (Remaining native-build failure in passing variants is an unrelated
"resident LLVM requires explicit path" env error, after MIR.)

## Root cause
src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl, text `.bytes()` gate (~line 2596):
any non-nil `receiver_declared_type` set `bytes_receiver_has_declaration = true`, so a non-Str
declared/inferred type (wrong inference from `trim()`) disabled the lowered-local `local_is_str`
proof and the call fell to custom dispatch -> unresolved. (Exact wrong HirTypeKind not observed.)

## Fix
Only `Str` or `Named` declarations are authoritative; other kinds fall through to `local_is_str`.
Regression spec: test/01_unit/compiler/mir/text_bytes_inferred_trim_receiver_spec.spl (not executed).

## Workaround
src/lib/common/sdn/parser.spl `parse`: `val trimmed: text = source.trim()` tagged @workaround.
Retire after fixed compiler is deployed.
