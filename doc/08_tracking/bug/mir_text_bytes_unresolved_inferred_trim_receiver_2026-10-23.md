# MIR: text `.bytes()` unresolved when receiver type is inferred from `trim()`

Status: open (compiler fix INSUFFICIENT — stage1-built stage2 still miscompiles the inferred form; workaround reinstated 2026-11-27)

## 2026-11-27 verification result (lane v7c, pin 06ba866385d5)

The workaround was retired by 41cbec8c26d (2026-11-25) while verification was
still pending. The stage2 compiler built by stage1 from pinned 06ba866385d5
miscompiles `val trimmed = _sdn_strip_leading_comment_lines(source).trim()`:
the stage2 compiler-test matrix `test_runner_build` row failed at dyn-lib
packaging with `src/compiler/00.common/simple.sdn: project.name is missing` —
the SDN parse of that manifest (37 leading comment lines, so the strip returns
a non-trivial slice) loses `project.name` inside the stage2 binary. Reproduced
outside the harness with the same stage2 binary:
`native-build --mode dynload --entry-closure --source src --entry src/app/test_runner_new/main.spl`
from the pinned root fails identically after link (321/321 objects). Probes
compiled BY that stage2 binary parse the same manifest bytes correctly both
from an embedded string and via `std.io_runtime.file_read` (len=2528,
NAME=simple-compiler-common), so the parser/file_read sources are correct and
the defect is in the stage1→stage2 compiled copy. The `method_calls_literals.spl`
`bytes_receiver_has_declaration` fix does not cover this path. Workaround
annotation restored at src/lib/common/sdn/parser.spl `parse`.

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

## Triage 2026-11-04 (MIR slice B)
Fix present on origin/release/1.0.0 in method_calls_literals.spl (`bytes_receiver_has_declaration`, only Str/Named authoritative, ~line 2887) with spec test/01_unit/compiler/mir/text_bytes_inferred_trim_receiver_spec.spl. Status: fix-implemented-verification-pending (needs stage2/3 native-build of the test runner; then remove the annotation workaround at src/lib/common/sdn/parser.spl:33).
