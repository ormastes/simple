# BUG-IT-8 — 40.mono: a generic call inside a string-interpolation segment is never counted or rewritten (undefined symbol at link)

Date: 2026-10-10. Status: OPEN. Lane: stage2 intensive tests. Stage2 49cbd00527..., release/1.0 @ b68c0c65708.

Repro (end-to-end): `test/fixtures/bootstrap/stage2_micro/micro_h/main.spl` —
`fn pick_second<C>(a: C, b: C) -> C: b`; `print "direct={pick_second(1, 2)} len={pick_second("a", "b").len()}"`.
Symptom: `[mono] generic_fns=1 call_sites=0 specializations=0 unresolved=0` — the two calls are not
SEEN by the pass — then `lld-link: error: undefined symbol: ...micro_h.main.pick_second` (rc=1, ~130 s).
First sighting: `micro_f` with five ordinary call sites plus one interpolated: `call_sites=6
specializations=3 unresolved=0` and the same undefined symbol — the counted sites were the
non-interpolated ones.

Reading: the call-site WALK in `monomorphize_integration.spl` (`rewrite_function` / `collect_*`) does
not descend into `HirExprKind.StringLit(_, interps)`; same family as the walker-shape gaps the pass's
own comments describe (plan 9.4), one expression kind short.

Ask: descend into interpolation expressions in both the walk and the rewrite; additionally fail
closed (E-MONO-033) when a template name survives in the emitted module while the counters report 0
unresolved — the counter/object-file mismatch is itself a bug.
