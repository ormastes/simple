# Must-Check Tiering Feature Expert

Keep interactive push validation near ten seconds. Do not add compiler builds,
full tests, QEMU/hardware work, or benchmark campaigns to the push driver. Add
expensive requirements to `config/check/must_check_gates.sdn` and produce their
evidence through `check-bootstrap-must-pass.shs`.

Compiler Stage 1-4 rows are push-blocking and may be promoted only after the
Stage 2/3 full-provenance verifier and exact Stage 4 post-bootstrap acceptance
oracle pass. Bootstrap completion then runs every automated registry row and
records its retained log; do not require a second operator command. PASS needs
a UTC timestamp and evidence reference. TODO and blocked rows remain visible
and never count as PASS.

## 2026-08-21 bootstrap repair handoff

The must-check producer remains correctly blocked until a fresh Stage 4 exists.
The latest receipt-bound Stage 3 completed all 954 streaming surfaces, proving
the transient type-pool owner repair, but HIR then failed first on an aliased
ASM signature dependency. Do not promote compiler rows from partial Stage 3
logs. Resume from
`doc/08_tracking/bug/stage3_callable_dependency_named_glob_precedence_2026-08-21.md`:
named dependency routes now outrank overlapping globs while same-precedence
conflicts still fail closed. Only after Stage 4 and essential-tool smoke pass
may `check-bootstrap-must-pass.shs` update the source-bound ledger.
