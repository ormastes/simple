# Stage 2 compiler-tests lane admitted beside a running Stage 3, and both died of memory exhaustion (W23)

Date: 2026-11-22
Host: DESKTOP-VMF96U6 (Windows 11, Hyper-V dynamic-memory guest, 64 GiB, #8931)
Ledger: `C:/dev/simple-release-boot-20261122/build/rboot/WORKAROUNDS.md` W23
Branch: `work/bootstrap-rss-cap-windows-20261122`

## Symptom

Stage 3 (cap 44 GiB) and the P4 lane (`admit-built-stage2-compiler-tests.shs`,
cap 24 GiB) were running at the same time on a 64 GiB host. Between 18:10 and
18:14, free RAM fell to 1.1 GB. MIR shard workers 1/9 and 2/9 hit an access
violation (0xC0000005) at claimed=0, and the P4 `cli_build` crashed (139) at
HIR 2240/4139.

## Root cause

Stage 3 refuses concurrent heavy work:
`scripts/check/lib/bootstrap-stage3/memory-admission.shs:750`
`bootstrap_stage3_memory_require_exclusive_heavy`, called at
`scripts/bootstrap/resume-stage3-from-admitted.sh:784`, refuses when
`native=1`. `scripts/bootstrap/admit-built-stage2-compiler-tests.shs` had no
equivalent check, so the lane started whether or not Stage 3 was running.
Stage 3's refusal only protects a Stage 3 that starts second.

## Fix

Before anything is superseded, `admit-built-stage2-compiler-tests.shs:64-85`
sources this script's own copy of the canonical facade and
`memory-admission.shs`. It then runs the same process scan
(`bootstrap_stage3_memory_append_processes`, Windows CIM or ps) and the same
gate (`bootstrap_stage3_memory_require_exclusive_heavy`).

- On a refusal it exits 75 with `admit-stage2: refused: concurrent heavy work ...`
  and the evidence path (`<output>/stage2-compiler-tests/<triple>/concurrency-scan.env`).
- A busy-host refusal never writes `rejection.env` and never moves an earlier
  rejection aside.
- If the scan itself fails, the lane also refuses (exit 75), as Stage 3 does.

**Override: none.** Stage 3 has no bypass for this gate (none in
`resume-stage3-from-admitted.sh` or `memory-admission.shs`), so none was
added. Run heavy lanes one at a time. `SIMPLE_BOOTSTRAP_STAGE3_PROCESS_SNAPSHOT`
is the shared fixture hook. In the ledger, `p4-after-p3.sh` got past Stage 3's
gate only because it never ran it.

Not fixed here: an allocation-failure access violation still reports a bare
0xC0000005, not OOM. That is a separate defect (ledger W23, second half).

## Specs

All cases are in `scripts/check/admit-stage2-compiler-tests-lane-test.shs`
(wired as `local-admit-stage2-lane` in `config/check/must_check_gates.sdn`):

- Reproducing: `busy`. A snapshot holding a Stage 3 `simple native-build`
  gives exit 75 and names `native=1`. The verifier does not run, and the prior
  rejection stays in place. The pre-fix script has no process scan at all, so
  it cannot refuse. This case was not run against the pre-fix script: the
  lane test stops at the earlier `capkill` failure.
- Generalization:
  - `peer`: two `bootstrap-from-scratch.sh` coordinators are refused.
  - `one-coordinator`: the lane's own caller is allowed and reaches the verifier.
  - The existing W12/W13 cases now run on an idle snapshot, so a live Stage 3
    on the test host never decides them.

Verified: `PASS — 17 admit-lane case(s) checked`.
