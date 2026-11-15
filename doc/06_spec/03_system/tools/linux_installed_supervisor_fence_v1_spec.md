# Actual installed Linux supervisor producer exclusion component

**Status:** AUTHORED_NOT_RUN. Runtime/build campaigns are exhausted; no native
fixture, service-manager operation, engine operation or spec ran in this lane.

**Executable:** `test/03_system/tools/linux_installed_supervisor_fence_v1_spec.spl`

**Requirements:** REQ-LINUX-SUPERVISOR-FENCE-001–003, scoped to the source
component described in `doc/05_design/linux_installed_supervisor_fence_v1.md`.

The disposable fixture must be installed by an administrator before execution.
The test itself must be the genuine MainPID of its installed supervisor service
under the dedicated service UID. The fixture needs the fixed protected machine
policy and supervisor profile, loaded legacy activation units, a running
dedicated provider service, the predelegated private service state directory,
and noninteractive system-manager authorization. The fixed
`/var/lib/simple/container` directory itself must be dedicated-service-UID-owned
0700 beneath root-protected `/var/lib/simple`, exactly as required by the actual
machine storage owner; there is no per-UID alternate state root. It must satisfy the closed
installation prerequisites in the design. No fixture is created by the test.

The first scenario reads the actual opaque installed profile, consumes its
reader, and closes a copied owner again. The second close must return the
recorded positive consumption result without calling the consumed reader;
the copied owner cannot read after consumption. This scenario covers normal
native close progress only, not injected native failures.

1. Open the actual protected installation and exclude its legacy activation
   routes. The native code authenticates the actual system manager, records
   prior state, masks the whole installed activation closure, reloads the
   manager, and stops each route through an exact returned job and successful
   `JobRemoved` result.
2. Observe actual masks, inactive/jobless units, collected service processes,
   empty or removed pinned cgroups, and the complete dedicated-UID process
   scan. Unknown processes refuse; no arbitrary process is killed. A failed
   current or installed-profile observation explicitly fails and returns before
   the competing mutating factory can run.
3. Attempt a second actual owner. It must refuse the same canonical global
   writer lock and release its pre-mutation cleanup.
4. Attempt to close without a real successor. Inhibition must stay retained;
   a copied owner still refers to the same actual canonical ownership. The
   scenario observes only exclusion-component diagnostics; it does not exercise
   machine admission.

The test mutates only the administrator-installed closure. It deliberately
does not unmask or restart anything. The administrator must tear down the
disposable fixture after collecting retained diagnostics.

**Not covered:** native success/failure ordering, authorization denial,
completion-before-reply, daemon replacement/disconnection, profile replacement,
unknown UID processes, partial masks, disappearing proc entries, failing
native closes, consumed-error diagnostics across a retained-partner retry,
unfiltered provider inventory, existing-charge adoption,
same-machine WAL admission, and successor handoff. These are pending real
fixture campaigns and subsequent source integration, not passing scenarios.
