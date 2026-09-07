# check-guard-wiring credited DEAD push-dispatch arms as wiring (2026-09-07)

Status: detector landed (blocking, green). Dead arms themselves NOT deleted —
see "Left open".

## Shape

`check-guard-wiring.shs` is the BLOCKING push gate that fails when a guard
script is reachable from no hook and no CI job. Its reachability model is
textual: a file that MENTIONS a guard's basename is an invoker of it.

The push tier's only enforcement surface is the `push,` rows of
`config/check/must_check_gates.sdn`, each dispatched by an exact-match
`'<id>:<mode>:<command>'` case arm in `run_manifest_push_gates`
(`scripts/check/check-push-must-pass.shs`). The manifest key is the only thing
that can select an arm, so **an arm no key produces never executes**. To the
textual model such an arm is indistinguishable from a live one — it names the
guard, it names `run_push_gate`, and it lives in a file that is reached — so
the gate reported those guards WIRED.

That is the same false-assurance shape as the wrong-tree defect, one level up:
*the gate that verifies wiring was satisfiable by wiring that does not run.*

How it surfaced: a lane deleted four unreachable arms as dead code and
`push-guard-wiring` immediately went red with **3 NEW unwired**. The lane
reverted rather than baselining, correctly.

## The dead arms at 0f2df78d307 (5 of 39)

| lines | class | key |
|---|---|---|
| 346-352 | no-manifest-row | `push-no-direct-rt:tree:sh scripts/check/check-no-direct-rt.shs` |
| 357-358 | no-manifest-row | `push-signature-type-import-provenance:tree:sh scripts/check/check-signature-type-import-provenance.shs` |
| 365-366 | no-manifest-row | `push-use-target-resolves:tree:sh scripts/check/check-use-target-resolves.shs` |
| 375-376 | no-manifest-row | `push-outline-parse-terminates:tree:sh scripts/check/check-outline-parse-terminates.shs` |
| 431-432 | duplicate-shadowed | `push-rt-api-groups:tree:sh scripts/check/check-rt-api-groups.shs` |

Root cause per class:

- **346-352** is superseded, not demoted. The live row carries `--roots src`, so
  its key is `push-no-direct-rt:tree:sh scripts/check/check-no-direct-rt.shs
  --roots src` and the arm at 415 answers it. The arm at 346 kept the pre-widening
  key and can never be selected. `check-no-direct-rt.shs` stays wired via 415.
- **357-358 / 365-366 / 375-376** are demotion residue. Each guard's manifest row
  now sits at `tier=bootstrap` under an id WITHOUT the `push-` prefix
  (`signature-type-import-provenance`, `use-target-resolves`,
  `outline-parse-terminates` — manifest lines 57, 53, 62), so no push key exists.
  Confirmed by history, not inferred: all three were demoted in one commit,
  `4f21072c336` "perf(check): move whole-tree gates to bootstrap", which rewrote
  `push-<id>, push, ..., tree` to `<id>, bootstrap, ..., automated` for each and
  left every arm in place.
  `.claude/rules/vcs.md` already documents why two of them are not push gates
  (use-target-resolves RED with 3,274 new; outline-parse-terminates ERRORs without
  a deployed `bin/simple`). The rows moved; the arms were left behind.
- **431-432** is a shadowed duplicate of the arm at ~427. The manifest ALSO carries
  two `push-rt-api-groups` rows (lines 32 and 36) with byte-identical keys, so the
  gate runs twice per push. Reported, not fixed — see "Left open".

## The honest count

**3 guards** lose their only recognised wiring once dead arms stop counting:
`check-signature-type-import-provenance.shs`, `check-use-target-resolves.shs`,
`check-outline-parse-terminates.shs`.

Measured on the real tree at `8e8f700117e` with the detector active, the
manifest credit below forced off, and the selftest bypassed. Two runs, because
the credit and the detector move the number in opposite directions and only the
second isolates this defect's own contribution:

    # baseline as landed (725) - both effects visible
    FAIL - 1596 guard(s) checked, 12 NEW unwired (725 baselined as known debt),
           0 stale/bad baseline or opt-out line(s), 0 copied hook(s)
    # the 12 = the 9 the manifest credit accounts for, plus the 3 below

    # the 9 temporarily restored to the baseline (734) - this defect alone
    FAIL - 1596 guard(s) checked, 3 NEW unwired (734 baselined as known debt),
           0 stale/bad baseline or opt-out line(s), 0 copied hook(s)
      unwired_guard=check-outline-parse-terminates.shs
      unwired_guard=check-signature-type-import-provenance.shs
      unwired_guard=check-use-target-resolves.shs

The baseline was restored byte-identical afterwards (`cmp` against
`8e8f700117e`). **Correction, stated rather than left to be found:** the commit
message on `8e8f700117e` quotes that second verdict as if it had been measured
before the push. It had not - it was measured after, and the transcript above is
the real one. The count and the three names were right; the provenance of the
quote was not, which in a record about gates that claim more than they measured
is exactly the thing not to leave implicit.

They were NOT baselined away and NOT opted out. Both files would have carried a
false statement: an opt-out asserts "deliberately not a gate", the unwired
baseline asserts "nothing invokes it", and all three ARE executed — by
`check-bootstrap-must-pass.shs:538` -> `run_automated_gate` -> `sh -c
"$_gate_command"` (:270-272), driven from CI by
`.github/workflows/rust-bootstrap-multiplatform.yml` through
`scripts/bootstrap/bootstrap-from-scratch.sh`. That chain was invisible to the
BFS because the manifest is a data file and `bootstrap-from-scratch.sh` is
outside the guard node set, so neither ever enters the frontier. Crediting
`tier=bootstrap, mode=automated` rows (commit A, `0f2df78d307`) records the
invocation that really happens; `mode=external-receipt` rows are validated, never
executed (`:513`), and are not credited.

Side effect of that credit, in the shrinking direction: nine guards a CI lane
genuinely runs on every bootstrap were sitting in
`guard_wiring_unwired_baseline.txt` as debt. Baseline 734 -> 725, deletions only.

## Trap worth remembering

A first draft of the new comment spelled `check-external-must-check-receipt.shs`
in prose. Because `check-guard-wiring.shs` is itself a reached file, that COMMENT
forged a wiring edge and accidentally wired 10 guards (that one plus 9 it
transitively names). Prose in a reached file is an edge. The existing
`*_note=`/`*_report=` prose filter does not cover comments — see "Left open".

## Left open

1. **The 5 dead arms are still in the dispatcher.** The detector neutralises
   them; deleting them is a separate, reviewable change. Deleting all 5 is safe
   under the detector (it already ignores them) and must be re-verified with
   `dead_dispatch_arms=0` plus a 0-unmatched-manifest-row check.
2. **Duplicate manifest rows** `push-rt-api-groups` at
   `config/check/must_check_gates.sdn:32` and `:36` — the gate runs twice on
   every push. Not touched here: any manifest edit risks the byte-match contract.
3. **Comments in reached files still forge edges.** The prose filter only drops
   `*_note=`/`*_report=` assignments. A `#`-comment naming a guard basename is
   indistinguishable from a call site. Narrowing that would change reachability
   tree-wide and needs its own measured lane.
4. **The BFS still traverses only guard basenames.** Non-guard entry points
   (`scripts/bootstrap/*.sh`) and data dispatch tables are invisible except for
   the one manifest credit added here.
