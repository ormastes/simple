# Focused FreeBSD reaper validation admission

Status: focused containment evidence is recorded below; full qualification is
blocked by the original pane spec's separate functional failure (14/15 passing).
Earlier admission sections describe historical candidates and pending checks
as they stood at that point; they do not override the terminal evidence below.
Preserve the existing focused-cycle history, including the original PTY
reproduction. The root coordinator authorizes the next bounded cycle after
independent review of the exact patch and this envelope. Never restart the
whole Phase 1 suite from this harness.

## Outer owner and memory boundary

Run the complete Python harness under **the exact candidate FreeBSD guard** in
enforce mode, with the existing 5,859,375 KiB compiler ceiling and a 300-second
outer deadline. An old SID-only outer guard is invalid here: it would reject
the real PTY fixture and make the containment result meaningless. No blanket
SID exception or monitor-only memory mode is part of this plan.

Nested guard cases detect the admitted bootstrap environment and use
`--session-mode=inherit`. Their native owners are subordinate reapers in the
outer hierarchy. Direct-owner fixtures inherit the outer session and remain
owned by its reaper. PTY and setsid descendants may change SID but remain in
the kernel hierarchy. The harness sentinel is outside each case's inner owner
and must survive every inner cleanup. The root may also maintain an independent
sentinel outside the outer owner. Do not kill a helper just because a tool
observation expires; inspect its exact PID/birth and receipt first.

The helper-loss fixture intentionally SIGKILLs only its own direct parent,
requiring non-quiescence from that inner guard. The outer owner retains any
resulting orphans. Workload fixtures also install a 12-second SIGALRM backstop;
the held nested-RSS fixture has a 20-second backstop and an explicit release
after its native sample is verified, covering allocation plus sampling budgets.
Failed-cleanup injection removes its marker in a finally block and
waits for the retained owner to finish; the harness never signals a cached
descendant PID or kills an unresolved owner as cleanup.

## Preparation (reviewed source, one compiler job)

Build `freebsd-reaper-faults.c` as a shared library in a unique owned evidence
directory using the guest native compiler with `-shared -fPIC`. The library is
test-only and explicitly supplied through `--fault-library`; production helper
code has no fault flags. Record compiler/kernel identity and library SHA-256.
The library intercepts only the injected native owner's procctl calls while a
case-owned marker exists: denied cleanup, denied query and saturated GETPIDS.

Run `perl scripts/resource/freebsd-reaper-protocol-test.pl` once for parser
negatives. Invoke the runtime harness from a pinned source checkout, using
absolute paths. Required original-pane admission arguments, before the trailing
`--original-command`, are:

- `--original-spec`: exact `test/01_unit/app/llm_caret/pane_backend_spec.spl` path.
- `--original-spec-sha256`: reviewed source hash.
- `--original-seed-sha256`: admitted Phase 1 producer hash.
- `--original-expected-examples`: independently inspected original example count.
- `--fault-library`: the prepared test interposer.
- `--original-command`: admitted seed followed by the original single-spec test
  command using that exact absolute spec path and interpreter mode.

The original result must have exactly one canonical Results summary and an
exact-path SPEC FILE VERDICT matching the admitted nonzero example count, all
passing, zero failures/skips/drops. The reported executed count comes directly
from the verdict, not an inference from the summary's total.
Spec and seed hashes are checked before and after that command. Missing original
admission or native fault injection is NOT_RUN, not full qualification.

## Evidence and limits

Preserve all receipts, native rows, PID/identity evidence, raw original test
output, cycle number and exact source/helper/producer/interposer hashes.
The nested reaper case independently records the native row of a distinct
32-MiB grandchild and checks its actual RSS, SID, parent and cleanup; cross-SID
counts alone do not qualify nested memory accounting.

Review Linux/other-platform compatibility separately on the same frozen patch;
the FreeBSD harness does not claim those platforms passed. Native syscall stalls
cannot be made bounded by a userspace timer: the parent fails its observation
deadline, while the native owner remains the reservation for unresolved work.
Each cleanup attempt has a userspace work/time bound and a five-second cooldown
after failure. Preserve that owner rather than claiming quiescence or restarting.

## Historical cycle 3 follow-up proposal (subsequently executed once)

Cycle 3 passed the real PTY fixture, then the outer owner closed its control
channel during the double-fork case: exit 89, quiescent=0, peak 237060 KiB.
There was no cap breach. The old receipt incorrectly released its reservation
because the owner had exited; no successful cleanup response had been received.
The source correction retains every unverified reservation, records the actual
native owner wait status, and reports failed writes without undefined-number
warnings. Native failure-stage diagnostics are added; the channel-close cause
itself remains unknown. No race correction or runtime PASS is claimed.

Before any extra runtime cycle, obtain an explicit exception to the user's
three-cycle limit. Proposed scope: run the new cleanup pipe/waitpid regressions
once, then run the remaining double-fork and ownership/fault cases followed by
the original 15-example pane spec under the same 5859375-KiB / 300-second outer
guard. Keep the three snapshot attempts, observation deadline, cleanup bounds,
kernel ownership checks and enforcement unchanged. Recompile the changed helper
with the real compiler; reuse the unchanged interposer and the prior 11 parser
checks by their recorded hashes. Preserve the previous PTY PASS as historical
evidence; no complete candidate qualification follows from that older helper.

Regression entrypoint (subsequently executed: eight checks passed):
`perl scripts/resource/freebsd-reaper-cleanup-test.pl`. Its six cleanup cases exercise
real pipes and child wait statuses: verified cleanup, EOF with zero/nonzero
exit, failed exit despite QUIET 1, owner SIGKILL, and a broken command pipe.
It tests receipt policy, not the FreeBSD kernel's containment behavior.
Two additional pipe cases check that sample/stop ERROR records retain their
diagnostic in the parent's failure, rather than becoming generic channel EOF.
Freeze the revised source hashes and an independently reviewed launch selection
before running; the existing full harness otherwise repeats the prior PTY case.

## Historical source correction after the first authorized extra cycle

The extra cycle exhausted all three snapshot attempts at
`owner-status-query 94849 3` (ESRCH); the outer guard exited 89 and retained its
unverified reservation. The diagnostic did not capture PID 94849's state.
Calling that process a zombie is an inference, not a demonstrated runtime cause.
No further build or runtime cycle is authorized by this correction.

FreeBSD releng/14.4 source establishes a concrete retry defect:
[kern_procctl.c](https://github.com/freebsd/freebsd-src/blob/releng/14.4/sys/kern/kern_procctl.c)
uses pfind for procctl PID queries and can report both REAPER and ZOMBIE from
GETPIDS; [kern_proc.c](https://github.com/freebsd/freebsd-src/blob/releng/14.4/sys/kern/kern_proc.c)
excludes zombies from pfind;
[kern_exit.c](https://github.com/freebsd/freebsd-src/blob/releng/14.4/sys/kern/kern_exit.c)
transfers a zombie reaper's descendants in proc_reap. Previously a failed sample
retried without draining waitable children, so an owned zombie could prevent
all three attempts from progressing. Skipping that branch could omit live RSS.

The source candidate moves the existing bounded wait drain from the successful
sample tail to the start of each attempt. Every attempt then rebuilds kernel
membership and birth-identity checks. The deadline, three-attempt limit, row and
depth caps, cleanup limits and RSS enforcement remain unchanged. Confirmed SZOMB
metadata emits `owner-zombie-unreaped`. A process that becomes a zombie after
that read may still report `owner-status-query` ESRCH. Another live parent's
unreaped child remains a blocker; this change does not claim to resolve it.

The following validation was proposed for a separately authorized, independently
reviewed frozen patch and subsequently executed in the cycle documented below.
Required regression: use a test-only interposer
barrier at the first owner GETPIDS call (after command-loop wait draining), make
a subordinate reaper exit while retaining a known live, allocated grandchild,
confirm the same PID/birth is SZOMB, then release the barrier. The next existing
attempt must reap the waitable owner, preserve its payload status if applicable,
and include the grandchild's kernel-confirmed membership and RSS in a complete
frame. No timing-only sleep should stand in for that barrier. A companion case
must keep a zombie reaper under a live non-reaping parent and require a failed
sample rather than omission of its branch. Both cases must preserve an external
sentinel and record terminal cleanup/reservation evidence. Also complete the
unfinished fork-race and remaining ownership/fault cases before the original
15-example pane spec. These were the validation requirements at proposal time. The terminal section
below records their subsequent results and the remaining original-pane failure.

## Canonical command topology and terminal evidence

The default harness and `--continuation-helper` still contain a nested
`kill-owner` case. They are **not canonical qualification entrypoints** under an
enclosing reaper guard. Killing that inner owner can leave a zombie reaper under
a live parent; the enclosing sampler correctly fails the unobservable branch.
That abort is not a passing isolated helper-loss test or a full-harness PASS.
Keep the exact tested harness frozen; do not rerun these entrypoints hoping the
outer sampler misses the zombie window.

Use a lightweight external controller and separate guarded commands. Every job
uses the candidate guard in `--session-mode=new --rss-cap-mode=enforce`, with
`--max-rss-kib=5859375 --interval-ms=100`. Compute each job's timeout from the
same original 300-second cycle deadline; launching another job does not reset
the deadline. The controller launches jobs and validates their evidence; it
does not host the workload itself. Preserve an external sentinel across jobs.

1. Run the deliberate held-parent zombie case as its own guarded command:
   `python3 scripts/resource/freebsd-reaper-regression.py --output NEGATIVE_DIR --fault-library ABS_SO --zombie-negative-helper ABS_HELPER`.
   Require exact PID/birth evidence in `zombie-held/before.txt` and
   `barrier.observed`, and either the fixture's successful assertions and quiet
   cleanup, or the independently reviewed enclosing-failure evidence path.
   An arbitrary exit 89 never qualifies.
2. For the positive prefix, a reviewed short driver calls the existing
   `zombie_reaper_case(helper, library, output, False, sentinel)` and
   `run_guard_case(guard, output, "fork-race", 124, sentinel)` functions under
   a guard. Persist their returned evidence. Do not invoke the default or
   continuation entrypoint, which would subsequently execute nested helper loss.
3. Run helper loss directly beneath its **sole** top-level candidate guard:
   `python3 scripts/resource/freebsd-reaper-regression.py --fixture kill-owner --output KILL_DIR`.
   Create `KILL_DIR` beforehand. The expected result is guard exit 89,
   `reaper_owner_wait_status=9`, `quiescent=0`, and
   `reaper_reservation_retained=1`. This proves truthful reporting of owner loss;
   it does not prove cleanup or release that reservation. Match the admitted
   native-owner identity and preserve the receipt.
4. Run the remaining cases under a new guarded command within the remaining
   budget: `python3 scripts/resource/freebsd-reaper-regression.py --output REMAINING_DIR --fault-library ABS_SO --remaining-helper ABS_HELPER`,
   followed by the existing exact `--original-spec`, spec/seed SHA-256,
   `--original-expected-examples 15`, and trailing `--original-command` admission
   arguments. No prior passing criterion is repeated by this phase.

The authorized cycle recorded held-zombie PASS with outer exit 0/quiescent 1,
waitable-zombie PASS with 55,760 KiB live-grandchild RSS and preserved payload
exit 7, and fork-race PASS with exit 124/quiescent 1. The historical continuation
then hit the nested helper-loss topology defect: the outer zombie PID matched
the inner admission's owner. Its abort was preserved, not counted as PASS.
The separate sole-guard helper-loss command produced the expected exit 89,
raw owner wait status 9, quiescent 0 and retained reservation 1.

The remaining seven ownership/fault cases passed: control EOF, malformed
command, parent death, nested RSS (55,740 KiB), cleanup denial, query denial and
saturated query. The original pane spec actually executed 15 examples, with
14 passing and one functional failure (`expected 14133`, got `#`). Its guard
exited 1 with quiescent 1; this was not a containment abort. Overall qualification
remains FAIL pending that functional repair. The earlier eight cleanup and
eleven parser checks were reused by recorded hashes, not rerun.

Evidence is under `build/reaper-wait-drain-cycle/evidence` and
`build/reaper-wait-drain-cycle/evidence-remaining`; the actual separate helper-loss
and remaining-case commands are recorded in `launch-remaining.py` and
`request-remaining.json` alongside them. This documentation correction executes
no command and grants no further runtime cycle.

## Subsequent original-pane repair

The separately published [pane fix #2735](https://github.com/ormastes/simple/pull/2735)
at `676ba1c40b7cae3404ec01a826b2dc6435c8ece8` subsequently passed the unchanged
original pane spec (15/15,1135ms) and POSIX fixture (3/3,1248ms), zero skips or
drops, under this unchanged native guard. Guard exit0/quiescent1, peak1841472KiB.
See the tracked containment report for exact source, fixture and seed hashes.
The earlier14/15 failure remains historical evidence; this is a separate focused
run, not a default all-cases harness or whole-suite PASS. No further runtime was
performed to publish these results. Landing still requires authenticated review
admission; the current legacy self-attestation workflow is insufficient.
