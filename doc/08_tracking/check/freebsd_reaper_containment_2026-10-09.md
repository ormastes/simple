# FreeBSD reaper containment: partial evidence, unqualified correction

STATUS: focused runtime criteria passed across the recorded runs; publication
remains blocked by unavailable authenticated review admission. This is a draft.
No whole-suite, production, or current-candidate runtime PASS is claimed.

## Immutable source provenance

Initial publication base: `9dedaa74c154ae32080a53a78065446e57bbe9c5` (`release/1.0`).
Updated publication rebased onto `b05fbaa6a1b4f9d9918f62af297d18d25eb9f07b`.
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
| `scripts/resource/freebsd-reaper-faults.c` | `9b910faf34bc7d7dd9d90c162ab24f0d64776d341586a8205a1b510da46d464c` |
| `scripts/resource/freebsd-reaper-protocol-test.pl` | `365f240bd2fa91272c36b27be4b825ef25df00819c757d6199e6d291ff3d9e9a` |
| `scripts/resource/freebsd-reaper-regression.py` | `fa3ef6625f43e5faff5637abcca8e0cfe0cc72ac18817b026d8cfcbe36929f0b` |

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
failure, not a proven runtime diagnosis. At initial draft publication the changed helper had **not been
built or tested**; the separately authorized follow-up below supersedes that
historical validation status. Earlier static reviews and historical fixture results do
not qualify this candidate.

At initial publication, pending verification included deterministic waitable and non-waitable zombie
reaper cases described in `scripts/resource/freebsd-reaper-validation.md`,
remaining ownership/fault fixtures, original pane test, and compatibility gates.
The user-provided three-cycle limit plus one explicit extra-cycle authorization
is exhausted. No additional BSD run, seed build, or whole-suite retry was made
for this publication. Do not merge until the required verification is complete.

## Authorized wait-drain follow-up: containment advances, pane assertion fails

The user subsequently authorized one focused cycle. Its initial frozen patch was
`1143c7eccce9e44c6b800218c877644598cfa70cba626ca36c054ccbf3a2ca40`.
The remaining-case selection-only addition produced tested patch
`19af00276e6972a242c289a9338f82732817d77eb7a2d0336fe108c987758514`.
Both used unchanged native source
`dfa0ed68d836bbf672ef7d5192cffd595dce49587e7125fd8fe38cff8d9f5885`.

The deterministic held-zombie case passed by rejecting an unobservable branch
and proving cleanup. The waitable-zombie case passed, retaining the live
leaf's identity and 55760 KiB RSS while preserving payload exit status 7.
Fork-race now passed with expected timeout 124 and quiescent=1.

Deliberate native-owner SIGKILL must run in its own top-level guarded job.
The initially nested owner-loss case interrupted its enclosing guard; it is
not a PASS receipt. The isolated case subsequently passed the failure-policy
assertions: owner raw wait status 9, guard exit 89, quiescent=0 and retained
reservation=1. That is verified fail-closed reporting, not successful cleanup.
The split jobs retained the single original 300-second deadline and memory cap.

Seven remaining fixtures passed: control EOF, malformed command, parent death,
nested RSS membership (55740 KiB), denied cleanup, denied query and full query.
Fault-library SHA-256:
`c377e5dc49e5e6a9c51d91f210b0dfabb411168b154e50a62dcc996ee0071130`.

The original pane test now ran every admitted example: **15 executed, 14 passed,
1 failed, 0 skipped, 0 dropped**. Its assertion reported
`expected # to contain 14133`. This is a functional pane-output failure, not a
successful original-spec criterion. Original-spec guard exit=1, quiescent=1,
peak RSS=1219384 KiB; outer continuation exit=1, quiescent=1.
The whole harness remains FAIL and whole Phase 1 remains incomplete.

Evidence is retained locally under `build/reaper-wait-drain-cycle/evidence/`
and `build/reaper-wait-drain-cycle/evidence-remaining/` in the source worktree.
Original spec SHA-256:
`ed09604a3e52bcdb24057cff9c3f5ca8592b80e99df9885ff640451a86ac3ac6`.
The default nested all-cases harness is not a qualified entrypoint: use the
separate guarded topology in the validation guide. Prior passing assertions
were reused; this report does not claim one default full-harness PASS.
At that point landing remained blocked pending the pane criterion and final review.
The subsequent pane repair below satisfies that focused criterion.

## Subsequent pane handoff repair: focused criterion passed

The separate pane correction, [PR #2735](https://github.com/ormastes/simple/pull/2735)
at `676ba1c40b7cae3404ec01a826b2dc6435c8ece8`, changes `src/app/llm_caret/pane_backend.spl` to
launch a private one-shot executable script instead of sending an exec command
to an interactive shell's terminal input. It is published separately from this
containment change; it does not modify the original pane spec.

Frozen production SHA-256:
`f6e4c898f52199e679a8016cfc456329ceaf89a9ecf2e6cd14465a4056231f36`.
POSIX fixture SHA-256:
`ac56750ae53523a76497d335ed4008707d1b870b7926638cd1a672145a26c04f`.
Both are based on release source `b05fbaa6a1b4f9d9918f62af297d18d25eb9f07b`.

The final FreeBSD run executed the unchanged original spec with **15/15 passed**
(1135 ms) and the new POSIX fixture with **3/3 passed** (1248 ms), no failures,
skips or drops. Two jobs ran under the candidate containment guard; guard exit
0, quiescent=1, peak RSS=1841472 KiB. Original spec and diagnostic seed hashes
remain those recorded above. Evidence lives in the pane worktree under
`build/pane-handoff-diagnostic/final-evidence/{request.json,verified-results.json}`.

These separate focused results resolve the observed pane-input failure and
satisfy the original-spec criterion with the corrected pane source. Historical
14/15 failure evidence remains unchanged. No default all-cases harness PASS,
whole Phase 1 PASS, stage2/native qualification, or cross-platform PASS follows.

Landing still needs authenticated exact-head review admission. The current
GitHub main-branch broker config says `configured=false` and signed receipts
unimplemented; its legacy self-attestation workflow cannot satisfy the canonical
v2 broker requirement. No legacy dispatch, fabricated approval, or bypass was
used for publication.
