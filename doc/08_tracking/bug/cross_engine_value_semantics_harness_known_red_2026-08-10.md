# Cross-engine value-semantics differential harness — landed KNOWN-RED (2026-08-10)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

**Spec:** `test/03_system/language/value_semantics/cross_engine_value_semantics_spec.spl`
**Probes:** `test/03_system/language/value_semantics/probe/p1..p9`
**Related:** `doc/07_guide/language/value_semantics_by_engine.md`,
`doc/08_tracking/bug/jit_struct_assignment_aliases_not_copies_2026-08-10.md`,
`doc/08_tracking/bug/aot_llvm_void_type_struct_probe_2026-08-10.md`

## What it is

One system spec runs each standalone probe on BOTH lanes via subprocesses —
interpreter (`SIMPLE_EXECUTION_MODE=interpreter bin/simple run <probe>`) and
JIT (`SIMPLE_EXECUTION_MODE=jit bin/simple <probe>`, pinned because the test
daemon exports `SIMPLE_EXECUTION_MODE=interpreter` and a bare child inherits
it) — filters output to `PROBE|` lines, and fails on any diff. Fail-closed: a
lane whose output lacks `PROBE|CONTROL=42` yields `AGREE=lane-failed`, never
agreement. Every verdict embeds binary identity (readlink -f, size, mtime,
`--version` banner) — the stale-binary episode of 2026-08-10 is why.

## KNOWN-RED enumeration (measured 2026-08-10, deployed pre-F1 seed,
`bin/release/x86_64-unknown-linux-gnu/simple`, 29,577,536 bytes,
mtime 2026-08-09 04:50)

Verdict: `11 total, 4 passed, 7 failed`. Expected failures:

| Probe | Position | Failure |
|---|---|---|
| p1 | plain assignment (S1) | AGREE=no — JIT aliases (`f.a=7.0`), interp copies (`f.a=1.0`) |
| p2 | nested struct field (S2b) | AGREE=no — shallow AggregateCopy residual; RED even on a fresh post-F1 seed |
| p3 | argument passing (S3) | AGREE=no |
| p4 | return value (S4) | AGREE=no |
| p5 | list element (S5) | AGREE=no |
| p6 | dict value (S6) | AGREE=no |
| p8 | `m[1][0]=9` (A2b) | AGREE=no — interp rejects the syntax (ic=1) after printing the control line |

Passing: binary identity, p7 (arrays), p9 (text), AOT-reachability (classified
`unreachable_timeout_or_killed` at 60s under host saturation on 2026-08-10;
the filed `llc-20` "void type only allowed for function results" blocker is
the other accepted classification — an UNKNOWN AOT failure fails the spec).

## Discrimination proof (both directions, 2026-08-10)

- Divergence direction: with the pre-F1 binary, the harness FAILED naming each
  of the 7 probes above, printing both lanes' filtered output per failure.
- Agreement direction: p7 and p9 (positions the lanes agree on) PASSED in the
  same run.
- Fail-open regression caught during bring-up: before the JIT lane pinned
  `SIMPLE_EXECUTION_MODE=jit`, daemon env contamination made both lanes run
  the interpreter and the harness reported a false 11/11 green. The pin plus
  this record are the guard.

## Operational notes

- Run: `SIMPLE_TEST_TIMEOUT=600 bin/simple test test/03_system/language/value_semantics/cross_engine_value_semantics_spec.spl`
  (relative path only; the default 120s daemon worker budget can be tight when
  the AOT probe times out at its full 60s cap).
- Do NOT weaken probes to go green.

## Unblock conditions (what turns it green)

1. Redeploy `bin/simple` from a post-F1 build (`735bbd4b606`, `cf992112a2d`,
   `9106761fe76`) — clears p1, p3–p6.
2. Fix shallow `AggregateCopy` (struct-typed field stored as pointer) — clears p2.
3. Either make the interpreter accept nested index assignment or make the JIT
   reject it — clears p8 (accepted-syntax parity).
4. AOT column stays informational until the llc-20 void-type defect is fixed
   and the host can complete a 60s native-build.

## Verification 2026-08-17 (content classification, fleet lane I)
NOT-A-DEFECT / working as designed — no action taken.
`test/03_system/language/value_semantics/cross_engine_value_semantics_spec.spl`
header (:6) reads: "Status: p2 deep-copy FIXED 2026-08-10 (recursive
`AggregateCopy.deep_fields`) — p8 remains KNOWN-RED by design", and :10 points
back at this very doc. The harness deliberately shells out to a JIT lane and
FAILS on any divergence (:16), and the header records the discrimination proof
in both directions (:19-21). This is an intentional known-red differential
harness, not a silent-wrong-result bug, and closing it red would remove real
coverage. Left exactly as is.
