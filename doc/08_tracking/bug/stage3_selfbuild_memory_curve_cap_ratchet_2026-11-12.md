# Stage 3 self-build memory curve and compiler-ceiling ratchet impasse (2026-11-12)

Lane: goal-mode bootstrap lane, worktree /home/yoon/dev/simple-boot-s3gen-20261112
(pinned source df719eff44cf, chase-fixed tip). Producer: s3gen stage2-admitted
compiler (1643 modules, sha family 559d473d).

## Measured per-phase memory curve (stage3 self-build, 1626-module closure)

Single whole-program compiler process; RSS sampled from the process-tree
watchdog receipt and live /proc:

| Phase | Peak RSS | Cap that survived |
|-------|----------|-------------------|
| parse (incl. 606KB switch_operators_calls.spl, ~12 min pathological) | ~3.9 GB | any |
| surfaces (build/alias/origins/freeze) | ~5 GB | any |
| HIR lowering (1626/1626 modules, 0 errors) | 10.2 GB | >= 12 GiB |
| MIR lowering | ~14 GB (two growth waves) | >= 16 GiB |
| codegen (per-module objects, aot-*.o) | > 16 GiB (killed at exactly 16777216) | >= ~26 GiB (projected) |

The 2026-10-13 mirtype-chase doc's "process dies SILENTLY with no
diagnostics -- suspected OOM" after the enum-contract pass is hereby
CLASSIFIED: same failure family -- the post-HIR phases (MIR, then codegen)
exceed the default ~8 GiB process-tree cap; exit 88 +
`status=rss-cap-exceeded` in the watchdog receipt, worker absent.

## The cap transport (why naive exports fail)

The stage3 native-build worker runs under `env -i` (pinned argv hash). Only
explicitly transported vars reach the compiler. The sanctioned pair:

- `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=<cap>` -- the enforced tree cap
  (validated: the watchdog receipt's max_rss_kib equalled this exactly).
- `SIMPLE_BOOTSTRAP_COMPILER_RSS_CEILING_KIB=<ceiling>` -- must be a STRICT
  RATCHET over the recorded previous ceiling (`>` previous, `<=` 3/4 host
  total AND `<=` 3/4 available), and `cap <= ceiling`.

Recorded-ceiling ratchet history this lane: 50331648 (stage2 transcript)
-> 58720256 -> 65011712 (62 GiB, current recorded).

## Current impasse (2026-11-12 ~23:20 KST)

Next stage3 needs cap ~26 GiB (codegen projection), so ceiling must be
>= 26 GiB and > previous 65011712. But the admission bound
`3/4 * MemAvailable` is ~61.5 GB while the recorded previous is 62 GiB
(68.2 GB) -- the ratchet cannot be satisfied until the shared host frees
~9 GB (other sessions hold ~8 GB of active work; fable-lane orphans
cleaned). This is a HOST-CAPACITY boundary, not a code defect.

## Auto-resume

`run-stage3f.sh` in the s3gen worktree polls /proc/meminfo and launches
`--resume-stage3-from-admitted` with ceiling=69206016 (66 GiB) /
cap=27262976 (26 GiB) the moment MemAvailable >= ~90 GB. All prior phase
caches (HIR 1626/1626 clean) are warm; the retry resumes at MIR/codegen.

## Evidence anchors

- stage3 watchdog receipts: logs/aarch64-unknown-linux-gnu/stage3-native-build.log
  (`status=rss-cap-exceeded`, `max_rss_kib=8388608|12582912|16777216`).
- HIR-completion witness: phase=hir done=1626/1626, 0 errors (this run,
  after the PR #8650 chase fix -- the chase family did NOT reproduce).
- MIR/codegen witnesses: phase=mir lines; 38 aot-*.o produced before the
  16 GiB kill.

## Correction (same day): ratchet baseline is the constant stage2 transcript

`bootstrap_tree_rss_ceiling_previous_kib` reads the STAGE2 admission
transcript's recorded ceiling (50331648 / 48 GiB) -- NOT the previous stage3
attempt's ceiling. Every stage3 resume compares against that same 48 GiB, so
any ceiling in (48 GiB, 3/4 * MemAvailable] is admissible on every attempt.
The "62 GiB recorded, cannot re-enter" impasse above was WRONG: 56 GiB
(58720256) re-admitted cleanly on 2026-11-12 ~23:30 with cap 26 GiB
(27262976).

Remaining gate for the final stage3 stretch: the lane's exclusive-memory
admission (concurrent native-build count must be 0 -- other sessions' spec
runs spawn short native builds). Auto-resume `run-stage3h.sh` polls both
conditions and launches when the box is quiet. Codegen peak projection
~18-26 GiB; cap 26 GiB carries the measured curve (HIR 10.2, MIR ~14,
codegen >16) with headroom.
