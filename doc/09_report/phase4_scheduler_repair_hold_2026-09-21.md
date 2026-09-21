# Phase 4 scheduler repair: HOLD

Base: `77d7a31aeba93b9545f71edd45388ee54279a80e` (PR #1224).
Owner: `/root/receipt_pr_review`, Astra xhigh.
Isolated worktree: `D:/wk-phase4-receipt-astra`.

**HOLD: the full canonical test did not pass. No Phase 4 admission or Windows-native containment claim is made.** Production and fixture source are frozen after three attempts; no fourth run is authorized in this session.

## Changes under review

Workers now write private receipt drafts. The parent reaps the exact supervisor,
rejects nonzero completion or invalid schema/config/source evidence, then commits
canonical receipts in matrix order. Dependencies require a parent-committed
marker for the current scheduler run. Worker admission binds the parent config,
matrix, and source-snapshot digests; current task snapshots must match that
config. The schedule is published atomically at `scheduler/schedule.tsv`.
Workers export matrix/task IDs, and metadata distinguishes supervisor PID from
the child session/group ID. Both C2 stdio rows remain blocked.

## Retained behavioral evidence

The first baseline attempt exposed the missing-task-ID fake-delay interaction;
it is diagnostic evidence only. With that unrelated delay disabled, the exact
baseline producer falsely returned zero after a successful worker's supervisor
exited 124. The extended canonical fixture correctly failed. This is the
isolated red reproduction, session 15453, log
`build/review/phase4-boundary-red-exact.log`.

The final attempt, session 98162, passed all four new supervisor/schema/source
boundary cases and the parent-committed dependency assertion. Its full matrix
terminalized all 49 rows: **44 PASS, 2 BLOCKED, 3 UNSUPPORTED, 0 failed**,
overall BLOCKED. Before the test stopped, it also passed schedule order,
concurrency bound, HOME/TMP ownership, native threads, C2 fail-closed evidence,
link receipt provenance, and source-test-count assertions.

It then failed `approved tool set was not linked exactly once`. The fixture's
global `FAKE_LINK_COUNT` contained **14** lines: **11** from the new boundary
scenarios and **3** from the original full matrix. The assertion assumes an
isolated full-matrix counter. This failure demonstrates fixture contamination;
it does not show fourteen links in the full matrix. The unapplied proposal
[`phase4_scheduler_fixture_isolation_proposal.patch`](phase4_scheduler_fixture_isolation_proposal.patch)
gives boundary invocations a separate counter. Its apply check passed; it has
not been applied or executed. The original exact-three assertion stays intact.

The remaining negative-result modes, resume/tamper cases, jobs=1 parity, timeout,
and TERM cleanup were **not reached**. They remain admission gates. The tests
ran as Linux/WSL controller fixtures, without C/C++ compilation.

| Retained artifact under `build/review/` | SHA256 |
| --- | --- |
| `stage4-matrix-baseline.shs` | `a71d960aabaa06de2dd9923838cbfab29472572168d713e3eed97027c0d22098` |
| `phase4-boundary-red-exact.log` | `012784f0427aead988cf9f42f9bda6c1969e6e34e17d9d742eab34dd31c91e4e` |
| `phase4-canonical-green-attempt.log` (failed attempt) | `c20166615c6ee73a7221b3d4c2621a1431a02d18bb3f70c63127c2de2f725478` |
| `phase4-full-summary.env` | `1329f830d67429636f4de890d1fc53229e44ef58511c3e8f6adebe3bd719fdf5` |
| `phase4-full-schedule.tsv` | `344cf69246de451cda66d29dc108a6e4102ebe9c70cf5ef32b0442aec176da41` |
| `phase4-final-fixture.tgz` | `0dd33048ee97cfbeb09fbe31ee1b672ce99b1885f7578ac11f514750b7b5f719` |

## Static review and remaining production risk

The four originally reviewed boundaries now have explicit implementation and
focused passing evidence. This is not a complete behavioral PASS. Static
self-review found an additional **P1**: scheduler state is allocated with
`mkdir -p scheduler/run.$$`, and successful runs retain that directory. A later
process reusing the PID can inherit old `committed/*` markers, defeating the
new per-invocation dependency boundary. This needs an exclusive fresh run
allocation plus a reproducing collision regression. It was not changed after
the freeze and must remain visible during independent exact-head review.

No time/RSS improvement is claimed. Actual before/after source-tree scans remain
per worker; the guide now records this cost instead of claiming an immutable
snapshot optimization. Shell syntax and working environment/artifact guards
passed, but they do not substitute for the unexecuted behavioral tail.

## Independent follow-up lanes

1. **Scheduler owner:** exclusive invocation directory/nonce allocation and a
   focused retained-state/PID-collision regression. Own production scheduler
   code and a separate canonical unit; require exact-head Astra review.
2. **Fixture owner:** apply the isolated-counter proposal without weakening
   assertions, then run the canonical contract once against the reviewed
   production follow-up. Retain negative/resume/timeout/TERM evidence and stop
   at the fresh task's explicit cycle limit.
3. **Containment reviewer:** independently inspect supervisor PID versus child
   session ownership and Windows/MSYS behavior using a separate focused harness.
   Do not infer Windows process cleanup from this Linux/WSL run.
4. **Performance/evidence owner:** define and collect equivalent jobs=1/parallel
   wall-time and max-RSS evidence after correctness gates pass; preserve current
   source validation while investigating repeated scans.
5. **C2 contract owner:** resolve protocol-root artifact/hash requirements and
   executable stdio evidence separately. Neither blocked row may be relabeled
   from static review or scheduler fixture results.

The bootstrap coordinator owns integration. These lanes must use isolated
worktrees and avoid concurrent edits to the same scheduler or canonical fixture.

## Rebase and publication scope

The frozen repair commit was `9f336c327fd55f773cc5c268dd7f2115864a0252`.
The user then authorized fetching and linearly rebasing onto
`origin/main` (`e0dd873da1b7828389db4eb60e82972cc8245313`). Rebase completed
as `c62c5ca6877c8312085a697d7f9cb819035bcc1d`. Two adjacent conflicts kept
both main's live-phase manifest configuration and this branch's job count.
The saved six-path manifest confirms **six present, zero lost**: four paths
are byte-identical; the scheduler and fixture also contain preserved upstream
changes. Evidence: `build/review/phase4-rebase-integrity.json`.

The 49-row behavioral results above belong exclusively to the frozen
**pre-rebase** source. No behavioral run was performed against rebased source.
Main adds four matrix rows (three tooling suites plus `phase_live_services`),
bringing the matrix to 53, but the merged canonical fixture expects 52 rows
and two blocked rows. This additional static source/fixture mismatch is an
admission blocker; the live-services prerequisite can add another blocked row.
Preserving these upstream changes does not establish their correctness.

PR #1224 may share this state only as **draft / HOLD**. The residual run-directory
P1, fixture counter proposal, upstream row-count mismatch, unexecuted behavioral
tail, and unmeasured parity/resources remain explicit follow-up gates.
