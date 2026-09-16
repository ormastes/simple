# Stage-2 native `text.starts_with` consumes the raw bool ABI incorrectly

## Status

Open and release-blocking. Three bounded planner compatibility expressions
failed; no unproven containment is retained in the release source.

## Reproduction

Build `src/app/cli/bootstrap_reason_planner.spl` with the admitted aarch64
Stage-2 compiler and execute it with the canonical Stage-3 authorization argv.
The process reports `bootstrap-policy-error: typed-reason-required` even though
GDB at `spl_main` proves `spl_arg_count() == 8` and `spl_get_arg(1)` is
`--bootstrap-reason=verify-landed-compiler-fix`.

Disassembly of `planner_arg_value` shows the result of
`rt_string_starts_with` compared against the tagged-bool value `0x13`, while
`src/runtime/runtime_native.c` returns raw C `0` or `1`. Therefore every prefix
test is false on this native lane.

The first containment attempt exposed a second facet: ordinary `text == text`
lowered to `rt_native_eq`, which returned false for byte-identical values when
one was a slice and the other a literal. GDB showed both values had length 19
and contained `--bootstrap-reason=`, yet `rt_native_eq` returned zero. The
attempted planner containment compared a bounded argument slice with an
equivalent prefix slice so both operands used the same runtime representation;
the stale compiler still rejected the canonical reason.

An attempted direct call to `rt_text_eq_any` was rejected: this Stage-2
compiler lowers `text as i64` to zero, so both operands arrived as nil. That
attempt produced no admission receipt and is not retained in source.

## Attempted RC1 containments

The release lane tried, in order: bounded slice-versus-literal equality,
`rt_text_eq_any` through `text as i64`, and bounded slice-versus-slice equality.
All three still emitted `bootstrap-policy-error: typed-reason-required`; the
second was specifically disproved because both casts became zero. The original
planner source remains authoritative until the compiler/runtime ABI is fixed.

## Required permanent fix

Align native method-call lowering and the core-C boolean return convention,
then add a native executable test that asserts both matching and non-matching
`text.starts_with`/`text.ends_with` results. Retire any temporary planner
containment only after that test passes with the admitted bootstrap compiler.
