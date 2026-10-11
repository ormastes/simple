# Compiler RSS headroom evidence — 2026-10-11

Attempt08, source26a5cb014d4bc61c8657f08799160f9f17834379, was correctly
terminated with exit88 at peak6308768KiB against cap6291456KiB. Its final
body-HIR counter was563/1214 with zero reported module failures. This change
admits a separately reviewed diagnostic ceiling; it does not fix or disguise
that memory regression and does not admit the failed compiler.

New controls passed once:27 parser/parity/refusal cases,7 additional
default/boundary/fixture cases and38 transcript/replay/clean-environment
handoff cases. The transport test's initial test-only PATH selection failure
was corrected to use one MSYS runtime; no product behavior was changed for it.
A tiny real Windows Job completed with exit0,
quiescent1 and peak10184KiB at cap/ceiling12582912KiB. Actual8jobs were declared;
fresh host total134094232KiB and MemFree52399824KiB supported admission.

Evidence is preserved at
`C:/dev/simple-bootstrap-storage/compiler-headroom-control-20261011`.
The Job receipt SHA256 is
`61af9b7c2f12c175a3bbc019b4274ff2c0d11952445b1c8b155b7c1ecc2af27a`.
Executed watchdog SHA256 was
`988ef5addee22acc24cd8b2e142132dd73a59dc5147e372634feac9439c9c08c`;
subsequent comment-only clarification does not change executed logic.

The earlier three nested-Job controls retain their original source hashes and
receipts. This change affects policy admission and receipt fields, not native
containment, supervisor launch or timeout branches. The Windows C Job helper
remains SHA256
`5a0c53c4584882656b4bf5d63ff4179cbe0735951ffd75bff923f4db54792ed7`.
No nested green controls were rerun. New compiler/Phase3/product qualification
is pending on the final integrated source, with the genuinely admitted old
parent; failed attempt08 must not be used as a parent.

## Generic timeout-owner followup

The separate `run-process-group-timeout.shs` owner also needs explicit native
ceiling forwarding. Normal Phase3 verification uses this owner for arbitrary
helpers, so the compiler-only ceiling and paired compiler cap must be removed
for those helper processes after syntax/pair validation. The generic helper
override and default policy remain unchanged; absence of the new ceiling
preserves legacy cap precedence. A nested compiler needs its own explicit
invocation rather than inherited elevation through a helper.

Nine new wrapper controls passed with the actual wrapper and real policy,
using an inert watchdog recorder to inspect argv/environment. They cover native
forwarding, helper stripping/default, generic helper override, unchanged legacy
cap, missing workers and invalid pairs. No workload or prior green test was run.
