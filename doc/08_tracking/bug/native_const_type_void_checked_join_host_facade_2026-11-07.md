# native: integer constant cannot define void in host_facade _checked join

- **Filed:** 2026-11-07
- **Severity:** P1
- **Status:** OPEN
- **Class link:** untyped_optional_arm_join_typed_as_i64_2026-11-06 (fix #7329 optional_join_word_slot does not cover this shape)

## Symptom

On stage3 s3_fable57s (which carries #7329), native-build of
`lib.nogc_async_mut.sosix.host_facade` fails with
`E-BACKEND-LLVM-CONST-TYPE: integer constant cannot define void` in
`sosix_spawn_checked` and `sosix_run_bounded_checked` (10 sites each).

Log: `C:/dev/p3new/s4/out/s4e_q/q0023/native-build.log.err` (batch q0023 of the s4e sweep).

## Analysis

Both functions are `_checked` wrappers that join Result/Option arms. The join slot
is typed void while an integer constant is defined into it, i.e. a join shape that
`optional_join_word_slot` (#7329) does not cover.

## Repro

Compile host_facade's closure natively (batch q0023), or a minimal `_checked` fixture
(Result/Option join returning an integer constant) to be written by the fixer.

## Acceptance

Reproducing fixture fails before fix; host_facade compiles natively; sibling `_checked`
join shapes covered by a regression fixture.
