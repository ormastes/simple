# SimpleOS six-target process mapping dispatch prerequisite

Status: implemented, unverified by user instruction.

The canonical signed target spellings now share one bounded loader policy.
Admission, joint loader reservation, load-plan address bounds, and scheduler
architecture matching consume that policy instead of maintaining divergent
architecture lists. Mapping-ready gates reject the three unfinished 32-bit
rows before joint reservation or scheduler token commit. The change does not
bypass the sealed installed-artifact catalog or mint execution authority.

Remaining completion blocker: x86-32, ARM32, and RV32 still require their native
initial-stack builder, address-space mapper, and user-entry handoff. Their policy
rows explicitly report that the process-image builder is not ready.
