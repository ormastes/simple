# MIR: text `.bytes()` unresolved when receiver type is inferred from `trim()`

Status: open (compiler fix applied and code-read-assessed COMPLETE for the
original repro shapes 2026-11-27 — see "2026-11-27 close-out assessment"
below; spec extended with call-result-receiver and sibling-method coverage,
still UNEXECUTED. Workaround annotation reinstated 2026-11-27 — but NOTE:
lane v7d proved the annotation does NOT fix the test_runner_build packaging
failure. That failure is the seed's `str.slice` -> `str_slice` rebinding;
see stage2_test_runner_libunit_project_name_missing_2026-11-27.md (the
2048-byte truncation theory was refuted). The annotation stays as cheap
insurance for the original .bytes() MIR issue until the removal precondition
below is met; this doc's compiler fix remains lane-verification-pending.)

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

## 2026-11-27 close-out assessment (code reading; no lane run)

Scope: does the `bytes_receiver_has_declaration` fix
(src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl ~line 3902)
cover the original repro, the parser.spl call-result shape, and the sibling
text methods at the parser.spl sites?

### Repro shape 1: `val trimmed = source.trim()` then `trimmed.bytes()` — COVERED
- `.bytes()` receiver is `Var(trimmed)`; `receiver_declared_type`
  (switch_operators_calls.spl:3309) returns the binding's registered HIR
  type. Whatever non-text placeholder inference recorded, the gate now only
  treats `Str`/`Named` as authoritative; anything else falls through to the
  lowered-local proof `local_is_str(prelowered_method_receiver)`.
- The `trim` lowering (method_calls_literals.spl ~5318/5433) emits
  `rt_string_trim` with dest type `MirTypeKind.Opaque("str")`, and the
  `val` binding preserves that MIR type for a str initializer
  (mir_lowering_stmts.spl:1998), so `local_is_str` (expr_dispatch.spl:1669,
  via `mir_type_is_str` Opaque("str")) is true. The call routes to
  `rt_string_bytes` instead of unresolved dispatch.
- Additionally, HIR binding inference
  (20.hir/hir_lowering/binding_types.spl:161) now records `Str` for
  `trim`/`strip` on a declared-text receiver, so the common case is proven
  at the declaration tier already.
- The `val tt: text = trimmed` copy variant from the repro notes is covered
  trivially: the explicit `text` annotation is a `Str` declaration.

### Repro shape 2: `val trimmed = _sdn_strip_leading_comment_lines(source).trim()` — COVERED
The `.bytes()` receiver is still `Var(trimmed)`; only the initializer
differs. For a call-result receiver, `hir_binding_method_call_return_kind`
(binding_types.spl:138-147) has no Var/typed receiver to read, so it returns
None — no wrong `Named` declaration can be recorded, and the gate falls
through to the same lowered-local proof. The trim call itself lowers through
the text-special arm because its own receiver (the user call, declared to
return text) proves text via `local_is_str` (method_calls_literals.spl:3573).
The only residual blocking case would be inference recording a wrong `Named`
type for a genuine text trim; no such path exists in
`hir_binding_method_call_return_kind` (Named returns only come from a
resolved user method's declared return).

Note: the "does not cover this path" line in the 2026-11-27 v7c section
above referred to the test_runner_build packaging failure, which lane v7d
re-root-caused to the seed's `str.slice` -> `str_slice` rebinding (a
different bug). It is not evidence against this fix.

### Sibling methods (starts_with / byte_len / slice) — NO SIBLING GAP
The defect class was specific to the `.bytes()` gate's inverted logic ("any
non-nil declared type is authoritative"). The sibling gates never had it:
- `starts_with`/`ends_with`/`contains` (~3500): proof is
  `local_is_str`/`local_hir_type_is_str` on the LOWERED local; a wrong
  non-Str declaration is never consulted as a blocker.
- `byte_len` (~4110), `slice`/`substring` (~4440): require
  `text_builtin_resolution_allowed`, proven from `receiver.type_ == Str` or
  the lowered-local text proof (~3573); again a non-Str declaration only
  fails to positively prove, it never vetoes.
So parser.spl lines ~68, 261, 284-285, 326, 358, 528, 533, 830 need no
annotation and no compiler change. The regression spec now locks this with a
sibling-methods case.

### Spec status
test/01_unit/compiler/mir/text_bytes_inferred_trim_receiver_spec.spl extended
2026-11-27: added the call-result-receiver shape and a
starts_with/byte_len/slice sibling case. Still UNEXECUTED — no deployed
self-hosted binary on this host runs the current source, and lane execution
is the real gate.

### Workaround removal precondition (src/lib/common/sdn/parser.spl:34)
Remove the `val trimmed: text` annotation only after BOTH:
1. a stage2 (or stage2ref) lane executes
   test/01_unit/compiler/mir/text_bytes_inferred_trim_receiver_spec.spl to
   PASS with a compiler built from source containing the
   `bytes_receiver_has_declaration` fix, and
2. the same lane native-builds the test-runner entry closure (the
   `test_runner_build` matrix row) from a tree with the annotation removed,
   with the SDN manifest parse (`project.name`) intact.
Until then the annotation stays as cheap insurance.
