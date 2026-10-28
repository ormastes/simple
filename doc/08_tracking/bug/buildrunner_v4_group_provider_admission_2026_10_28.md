# BuildRunner V4 group provider admission and population proof

Baseline: release/1.0.0 `9a8952b7211`. Date: 2026-10-28.

The native BuildRunner positive gate remains blocked. Darwin V4 reports
unavailable; Linux V4 accepts LeaderOnly and rejects ProcessGroup/Tree with
ENOTSUP before executable acquisition. The guard must remain in place.
No phase2 compiler was rebuilt for this investigation.

## Fixed population decoder defect

The separate Linux grouped broker accepted `populated 0junk`, `populated 00`,
and conflicting duplicate population lines as a tree-empty observation.
Its decoder now requires exactly one complete `populated 0` or `populated 1`
line. Embedded NULs, trailing spaces/tabs, incomplete lines, duplicates, invalid values and
missing population fields fail with EPROTO without modifying the output.
Unknown complete fields remain allowed for kernel interface extensibility.

The new fixtures reproduced the old decoder failure at `assert(!valid)`.
The fixed population fixture and the full V4 host selfcheck passed on native
Linux aarch64 in an isolated Docker container. The V4 fixture now verifies
that ProcessGroup/Tree rejection returns neither a PID nor a ticket, claims
no tree-empty time, and never acquires the executable pin. An initial x86
emulation run could not run the existing ptrace lifecycle checks; this is not
recorded as provider failure or positive evidence.

Reproduce on Linux with a C compiler and permitted ptrace:
`sh scripts/check/check-process-v4-group-admission.shs`.
The script bounds each executable with timeout and returns 77 on other hosts.
These C host checks are component evidence, not Pure Simple or SPipe admission.

## Why the existing broker cannot be promoted into V4

`runtime_linux_group_owner_impl.h` uses CLONE_INTO_CGROUP for atomic placement
and a pinned cgroup directory for population observations. These establish
initial placement and group observation, but not permanent containment.
The executed process retains the broker's credentials and access to the
cgroup filesystem. No credential boundary or equivalent mechanism prevents
migration. Closing inherited cgroup descriptors alone does not prevent the
process from opening a writable cgroup path. Thus population=0 can mean
escape rather than all descendants retiring.

Its post-clone error path also ignores cgroup.kill failure, waits only for the
leader, ignores failed group removal, and closes ownership descriptors.
A failed start can therefore lose cleanup authority; an unbounded waitpid
can also hang. A Luna review independently confirmed this cleanup gap.
These are unresolved blockers, not fixed by the population decoder change.

The next provider needs an explicit exclusive containment authority: worker
credentials or another enforced boundary must deny cgroup migration, placing
the child before execution. It must retain a cleanup ticket through every
post-spawn failure and establish populated=0 before retiring ownership.
V4 also needs exact exec/wait4, bounded capture, frozen replay and exact ACK
integration, followed by escaping-descendant and failed-cleanup adversarial
fixtures. The existing mechanism options remain unselected; this change
neither narrows scope nor enables the broker as a V4 fallback.
