# Stage3 containment on WSL without a systemd user manager

Ubuntu-22.04 has a writable cgroup-v2 hierarchy and an enabled enclosing memory
controller, but no systemd user manager. The canonical Stage3 resume therefore
refused containment before compiling. Memory admission had passed with explicitly
bounded 16384 MiB headroom and an 8192 MiB process limit.

## Explicit backend

The default remains `systemd`. A privileged launcher may invoke
`scripts/bootstrap/lib/stage3-cgroupfs.py root-run --high 16384 --maximum 8192
--user ormastes --receipt <fresh-user-writable-D-path> -- <canonical-resume-command>`
with `/usr/bin/python3 -I`. The helper creates a fresh root-owned private domain,
enables memory only there, installs limits before delegation, and starts the
canonical coordinator as the ordinary user in its supervisor leaf. It remains
outside that hierarchy for cleanup. No enclosing controller is modified.

Only the private parent membership file and worker membership/kill files are
delegated. The worker joins itself before exec; the existing canonical worker
also verifies kernel membership and exact memory limit readback. Limits, sibling
membership, hierarchy creation, and controller configuration remain protected.
The helper must match its blob in the admitted source HEAD. Helper and Python
hashes are then recorded and checked by the resume path. Existing
memory admission, exclusive-heavy policy, virtual-memory ceiling, RSS guard,
runtime headroom watcher, source/runtime authority, and output lock remain active.
The backend does not permit same-OS concurrent heavy jobs forbidden by admission.

Every root-launch exit kills and drains both owned leaves before removing the
fresh hierarchy. Canonical worker completion also drains its leaf before the
usual inactive check and lock release. Cleanup failure retains the canonical
lock and returns failure. Receipt writing uses the ordinary user identity and
exclusive creation after privileged cleanup.

## Evidence and limits

The real kernel regression `test/00_quick/bootstrap/stage3_cgroupfs_kernel.py`
passed once on Ubuntu-22.04: nonroot UID/capabilities, no inherited cgroup FDs,
exact 64/128 MiB readback, denied limit/controller/escape writes, self migration,
and descendant cleanup. Both leaves were empty and removed; actual exit was 0.
Evidence: D-backed ext4 `stage3-cgroupfs-kernel-cycle1-20260929.json`.
Shell syntax passed for the resume script. This component evidence is not a
Stage3 compiler build, bootstrap qualification, Windows claim, or Stage4 result.
Distinct terminal-case regressions passed: a faulted 256 MiB allocation under
128 MiB `memory.max` exercised real kernel max enforcement (2439 max events,
resident usage bounded, no OOM kill because reclaim/swap succeeded); coordinator
launch failure and root-supervisor TERM each drained and removed both leaves.
Evidence: `stage3-cgroupfs-terminal-cases-cycle3-20260929` on the D ext4 image.
Two preceding fixture attempts are preserved: a lazy allocation and then soft
`memory.high` reclaim did not exercise the hard maximum; the initial evidence
directory also correctly rejected unprivileged receipt writing. The final
fixture faults every page, places high above max, and uses user-owned evidence.
Signal handlers are installed before provisioning or child launch.
