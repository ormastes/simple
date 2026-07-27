# BUG: sys_restart had no ceiling — a crash-loop was a privilege-escalation primitive

- **Status:** FIXED 2026-07-27 (lane CESC)
- **Severity:** HIGH — capability + filesystem escalation
- **Component:** `src/os/services/container/container_manager.spl`
- **Found by:** `test/01_unit/os/services/container/container_escape_suite_spec.spl`
- **Related:** master plan §21 (restart drops stale grants),
  `src/verification/os_enforcement/ContainerIsolation.lean`

## Summary

§21 says nothing may SURVIVE a restart. `sys_monitor` / `sys_stop` implemented
that correctly: on exit the granted pouch is emptied and the kernel view is
collapsed to rootless. But §21 says nothing about how much a restart may ASK
FOR, and `sys_restart` enforced no bound at all — it assigned
`granted_caps[idx] = reacquired` and built the view from whatever `root` the
caller named.

Because the §21 teardown had already emptied `granted_caps[idx]`, there was no
surviving record of the container's original authority, so nothing could bound
the re-acquisition. The §21 fix is exactly what removed the ceiling.

Net effect: a container that crashes on purpose comes back with more authority
than it was ever created with.

## Minimal repro (pre-fix)

```
var w = ContainerWorld.new()
val c = w.sys_create("victim", "/containers/victim", [100u64], "sha256:base",
                     1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
w.set_restart_policy(c, "on-failure", 3)
val first = w.sys_start(c)
w.post_monitor_report(c, "crashed", 137)
w.sys_monitor()

# the escalation: ask for anything at all.
val again = w.sys_restart(c, ["cap.fs_read", "cap.sys_admin", "cap.host_net"],
                          "/", [100u64], 1024u64, 4096u64, 100u64, 64u64)

# PRE-FIX observed:
#   again.caps                       == ["cap.fs_read","cap.sys_admin","cap.host_net"]
#   w.allows_path(c, "/etc/shadow")  == true      <-- host filesystem
```

## Fix

Two ceiling columns frozen at `sys_create` and never widened:

- `ceiling_caps: [[text]]` — the create-time grant, the maximum this entity may
  ever hold;
- `ceiling_roots: [text]` — the widest subtree it may ever resolve through.

`sys_restart` now attenuates against both:

- `attenuate_caps()` keeps only caps present in the ceiling (intersection —
  never amplifies, mirroring `oci_import.caps_intersect_isolated`);
- `clamp_root()` accepts a root at or BELOW the create-time root and collapses
  anything wider back to the ceiling root.

Narrowing on restart still works (proven by a dedicated spec case), so the
clamp is an attenuation, not a blanket reset.

## Known remaining gap (NOT fixed, deliberately)

`sys_restart` still does not consult `restart_eligible()`: a caller may restart
a container whose `max_retries` is spent, or one that is not in `exited` state
at all. That is a POLICY bypass, not an authority escalation — with the ceiling
in place the restarted container can never exceed its create-time authority —
so it is recorded here rather than changed, because tightening it would alter
the manager's public lifecycle contract and belongs with the supervisor wiring.
