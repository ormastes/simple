# Native owned-lock namespace origin

Source: `src/runtime/test/runtime_file_lock_owned_origin_v2_test.c`.
Evidence: all five scenarios **NOT_RUN**. No compiler/native test slot was
allocated or used. This is an authored source manual, not generated evidence.

The positive control starts an ordinary child with a virgin registry. The four
namespace cases start a fresh actual Linux user/PID namespace whose first child
is really PID 1. Initial identity proof always uses the real namespace object;
there is no fake getpid, caller-supplied identity flag, or namespace reset.
Denied namespace creation fails/blocks the test instead of skipping it.

1. Require actual ordinary native acquisition, a successful established-origin
   stat check with preserved errno, held state and successful release. This
   catches inverted stat-success polarity independently of refusal cases.
2. Acquire an actual native writer lock in outer PID 1 and hold its registry
   gate. Fork inner PID 1 in another PID namespace. Require a different actual
   device/inode identity and bounded UNKNOWN refusal for inherited state and
   release, with no new acquisition or native close. Only the unchanged parent
   releases its original gate and lock.
3. Establish the real owner, hold its gate and inject one later stat failure.
   Restore the real observation. Require sticky refusal without a new probe or
   gate/native access; the actual writer lock stays contended until process
   death.
4. Repeat with an inode mismatch returned by the later-stat test adapter, then
   restore the actual inode. Require the same permanent quarantine. This is a
   mechanism case, separate from the real namespace collision in case 2.
5. Fail the first post-poll origin observation after actual native lock
   acquisition. Require the original positive token and atomic UNKNOWN slot to
   retain the opened handle, no native close, no admission and actual writer
   contention. Do not retry the descriptor or fabricate an absence receipt.

Signal alarms bound regressions that would enter an inherited held gate. The
outer observer checks native lock availability only after the entire owning
process dies. That observation does not claim a successful owner cleanup turn.
The existing Linux ordinary-fork source regression now requires UNKNOWN rather
than stale/nil release for a positive inherited token.
