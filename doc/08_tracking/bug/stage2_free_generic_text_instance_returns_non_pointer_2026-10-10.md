# BUG-IT-5 — stage2 native path: free generic fn specialized at `text` returns a non-pointer (wrong code)

Date: 2026-10-10. Status: OPEN. Lane: stage2 intensive tests. Stage2 49cbd00527..., release/1.0 @ b68c0c65708, BOOT=1.

Repro (end-to-end): `test/fixtures/bootstrap/stage2_micro/micro_b/main.spl` —
`fn pick_second<C>(a: C, b: C) -> C: b`; `val pick = pick_second("a", "b")`; `print "... pick={pick} ..."`.
Observed: build rc=0, run rc=0, stdout `adder=15 twice=14 sum_i=6 pick=140702839497239 res=ok:9
err=negative trait=14` — every other field correct; `pick` should be `b`.
`[mono] generic_fns=1 call_sites=2 specializations=2 unresolved=0`: both `pick_second$str` and
`pick_second$i64` exist; the `$str` instance's result is consumed as an i64 (a heap pointer value).

Narrowing: `micro_f/main.spl` USES the text instance (`.len()`, `==`, typed/untyped let, non-generic
twin, i64 and struct instances). Result: build rc=0, then SEGV rc=139 with no output — once the
value is dereferenced the process dies. The i64 instance (`pick_second(1, 2)` -> 2) and the struct
instance (`pick_second(Acc(..), Acc(n: 103)).n` -> 103, `free_generic_fn_two_module_native_spec`)
are correct, so the defect is specific to the `text` instantiation: most likely the `C = str`
specialization's return/let slot lowering to i64 while the body produces a text pointer.

In-process: `generic_fn_specialization_breadth_spec` shows 40.mono produces `first_or$str` with zero
diagnostics, so the fault is downstream of the pass's statistics (HIR rewrite types / 50.mir / codegen).
