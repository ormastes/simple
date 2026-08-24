# SimpleOS six-target process mapping dispatch prerequisite

Status: implemented, unverified by user instruction.

The canonical signed target spellings now share one bounded loader policy.
Admission, joint loader reservation, load-plan address bounds, and scheduler
architecture matching consume that policy instead of maintaining divergent
architecture lists. Mapping-ready gates reject the three unfinished 32-bit
rows before joint reservation or scheduler token commit. The change does not
bypass the sealed installed-artifact catalog or mint execution authority.

Remaining completion blocker: x86-32 and RV32 still require completion of their
native initial-stack/address-space/adoption paths. ARM32 now has a four-byte
initial stack, explicit address-space mapper, load-lifecycle binding, and
non-authorizing pre-token adoption reservation/rollback, but still lacks the
scheduler-owned move and real user-entry/SVC/reap handoff. All three policy rows
therefore still explicitly report that the process-image builder is not ready.
