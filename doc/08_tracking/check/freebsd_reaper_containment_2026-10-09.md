# FreeBSD reaper containment: partial evidence, unqualified correction

STATUS: BLOCKED for release qualification. This is a draft source publication.
No whole-suite, production, or current-candidate runtime PASS is claimed.

## Immutable source provenance

Publication base: `9dedaa74c154ae32080a53a78065446e57bbe9c5` (`release/1.0`).
Original source base: `e23da7a417f3c970467db463d40af20bc764110a`.
Tested candidate patch SHA-256:
`2704f2ae45f9afe7db6d854695f00071a5ebcd4ff1966455588f7810541adf33`.
Transferred correction patch SHA-256 before these documentation updates:
`81eeff960bc9696f6dfffe90dfff9000e7cbea5d337efc75ef4884ee18f213c1`.
The production/helper and test sources below are transferred byte-for-byte.

| Source | Current SHA-256 |
| --- | --- |
| `scripts/bootstrap/bootstrap-session-exec.c` | `dfa0ed68d836bbf672ef7d5192cffd595dce49587e7125fd8fe38cff8d9f5885` |
| `scripts/resource/process-tree-rss-watchdog.pl` | `76b1bacc94f4c1e483f4fe5d2dea4203947432bc33b17a4553015f7840f54499` |
| `scripts/resource/freebsd-reaper-cleanup-test.pl` | `d333e4a34e182a25db7afd1ab3866071eb307b88c91d880184aa84c0910e42ef` |
| `scripts/resource/freebsd-reaper-faults.c` | `c501907c91a78912a1b7bab565a7f2adca1bda48ac0b7edda8399c0e4e80b2b7` |
| `scripts/resource/freebsd-reaper-protocol-test.pl` | `365f240bd2fa91272c36b27be4b825ef25df00819c757d6199e6d291ff3d9e9a` |
| `scripts/resource/freebsd-reaper-regression.py` | `b0281f5767e3c8389f878cd0250fecc5a0abe30144d3855ef8654f05cdc0c6b6` |

Admitted original Phase 1 seed SHA-256:
`daadf4c854c0ef8d5a0d9cf33379c3dd28a1f7ba7c93a6b915c77973943fb721`.
Evidence retained in the source worktree under
`build/reaper-astra-correction/{freeze.json,runtime-status.json,evidence/}`.
These local paths identify preserved evidence; they are not public CI artifacts.

## Actual authorized extra-cycle result

Eight pipe/wait-status cleanup regression checks passed. Eight runtime fixtures
produced their expected exit receipts and individually reported `quiescent=1`:
PTY, double-fork, root-exit, nested reaper, twenty trees, RSS limit, timeout,
and TERM. These results apply to candidate `2704f2ae`, not the latest helper.

The fork-race fixture was interrupted. The outer guard exited **89**, with
peak RSS **899672 KiB**, `quiescent=0`, and `reservation_retained=1`.
Diagnostic: `ERROR 1 94733 sample owner-status-query 94849 3 3 0 -1 -1`.
The query reported ESRCH; the failing PID's actual state was not captured.
No combined harness result exists. The original 15-example pane test and
remaining fixtures are **NOT_RUN**. Whole Phase 1 is still incomplete.

## Latest correction and remaining gate

The latest correction moves the existing bounded wait drain to the beginning
of each snapshot attempt and diagnoses identity-confirmed zombie owners.
The snapshot attempt count, bounds, memory enforcement and cleanup policy are
unchanged. Zombie ownership is a source-supported hypothesis for the prior
failure, not a proven runtime diagnosis. The changed helper has **not been
built or tested**. Earlier static reviews and historical fixture results do
not qualify this candidate.

Next verification requires the deterministic waitable and non-waitable zombie
reaper cases described in `scripts/resource/freebsd-reaper-validation.md`,
remaining ownership/fault fixtures, original pane test, and compatibility gates.
The user-provided three-cycle limit plus one explicit extra-cycle authorization
is exhausted. No additional BSD run, seed build, or whole-suite retry was made
for this publication. Do not merge until the required verification is complete.
