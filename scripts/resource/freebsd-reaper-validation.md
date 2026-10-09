# Focused FreeBSD reaper validation admission

Status: current wait-drain correction is UNRUN and not release-qualified.
See the dated evidence report in
`doc/08_tracking/check/freebsd_reaper_containment_2026-10-09.md` for the
previous candidate's partial runtime results and terminal failure.
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

Regression entrypoint (subsequently executed: eight checks passed in the
authorized extra cycle, before the latest wait-drain correction):
`perl scripts/resource/freebsd-reaper-cleanup-test.pl`. Its six cleanup cases exercise
real pipes and child wait statuses: verified cleanup, EOF with zero/nonzero
exit, failed exit despite QUIET 1, owner SIGKILL, and a broken command pipe.
It tests receipt policy, not the FreeBSD kernel's containment behavior.
Two additional pipe cases check that sample/stop ERROR records retain their
diagnostic in the parent's failure, rather than becoming generic channel EOF.
Freeze the revised source hashes and an independently reviewed launch selection
before running; the existing full harness otherwise repeats the prior PTY case.

## Source correction after the authorized extra cycle (not run)

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

Next validation requires separate explicit authorization and an independently
reviewed frozen patch. Required unrun regression: use a test-only interposer
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
15-example pane spec. These are validation requirements, not executed tests or
PASS claims; the prior successful fixtures do not qualify this changed helper.
