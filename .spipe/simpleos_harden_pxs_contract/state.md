# Lane PXS — POSIX Server tier-1 port-enabling contract

Master plan section 9.3 (port-enabling order) + Phase 4. Typed pure-Simple
model + spec for the FIRST tier of the port-enabling order, so LLVM / OpenSSH
/ SQLite / build-system ports have a typed target and the honest
supported/unsupported status is machine-checked. This is NOT a real libc
build — no live syscalls.

## Files (working copy only — NOT committed)
- `src/os/posix/posix_server_contract.spl` — typed contract + model.
- `test/01_unit/os/posix/posix_server_contract_spec.spl` — spec, 19 examples.
- `.spipe/simpleos_harden_pxs_contract/state.md` — this file.

No name collision with existing `src/os/posix/` files; `posix_server_contract`
is a new module. Imports/reads only from `os.posix.errno`; does not duplicate
or edit existing posix files or P5's `posix_profiles.md`.

## Facility / status table (aligned to P5 `doc/02_requirements/os/posix_profiles.md`)

| Facility | Profile | Status | Implemented | Backing |
|---|---|---|---|---|
| posix_spawn | B | supported | yes | os.kernel.process_compat + simpleos_process.c |
| execve | B | supported | yes | os.kernel.process_compat + simpleos_process.c |
| waitpid | B | supported | yes | os.kernel.process_compat + simpleos_process_wait.c |
| fork | B | partial | yes | os.kernel.process_compat + simpleos_fork.c (COW fork not yet) |
| signals (kill/sigaction) | B | supported | yes | signal_compat + signal_dispatch + simpleos_signal.c |
| process_groups (setpgid/getpgid) | C | unsupported | no | absent — no symbol wired |
| dup2 (full FD semantics) | B | supported | yes | os.kernel.fd_io + simpleos_fs.c |
| pipe | B | supported | yes | os.kernel.pipe_compat (ring buffer + notification) |
| af_unix_socketpair | C | unsupported | no | absent — no sys/un.h impl |
| poll | B | supported | yes | select_compat + simpleos_poll.c |
| select | B | supported | yes | select_compat + simpleos_poll.c |

Status counts: supported 8, partial 1 (fork/COW), unsupported 2
(process_groups, af_unix_socketpair). All statuses trace to P5's matrix rows;
`fork` downgraded to partial because COW fork sits at the END of the section
9.3 order (extended compat), and `process_groups` is unsupported because P5's
matrix has no setpgid/getpgid row.

## Section 9.3 order as a dependency model (`can_enable`)

Port-enabling order encoded as prerequisite edges:

    waitpid -> signals -> process_groups -> dup2(full FD semantics)
                                             -> pipe
                                             -> af_unix_socketpair
                                             -> poll
                                             -> select

`can_enable(name, enabled_set)` returns false if any prerequisite is not in
`enabled_set`. This makes the ORDER a machine-checked constraint: `poll` (and
`af_unix_socketpair`) are denied until the full-FD-semantics tier `dup2` is
enabled, allowed after. Tier-1 roots (posix_spawn/execve/waitpid) have no
prerequisites.

## Honesty rule (fail-closed, mirrors P5)

`honesty_violations()` machine-checks that no facility with `implemented:
false` reports `supported`. `find_facility()` returns an `unsupported`
fail-closed default for unknown names. `profile_supported_set(profile)`
returns only genuinely-supported facilities at or below that profile on the
cumulative POSIX axis (A native = empty of POSIX adapter symbols; C = B+C
supported set).

## Spec verdict

`19 examples, 0 failures` (5 + 5 + 5 + 4) via
`/tmp/pxslane/bin/pxsjob run test/01_unit/os/posix/posix_server_contract_spec.spl`.

Fail-once proof: flipping `af_unix_socketpair` to `status: "supported"` while
`implemented: false` produced `3 failures` across the honesty-invariant,
fail-closed-status, and profile-membership examples; restoring to
`unsupported` returned to 0 failures. The honesty check is load-bearing.

## Next increment (multi-session — the real work behind each row)

This lane is the TYPED TARGET. The actual libc implementation of each tier-1
facility is separate, multi-session work:

1. **process_groups (setpgid/getpgid/setsid)** — no kernel session/pgroup
   concept exists; needs a kernel process-group table + syscalls, then a libc
   shim. Required by job-control shells and by OpenSSH.
2. **af_unix_socketpair** — no `sys/un.h` wiring beyond the header; needs a
   local (in-kernel) AF_UNIX endpoint over the existing notification/IPC
   layer + `socketpair()`/`bind()`/`connect()` for AF_UNIX. Required by many
   build systems and by dbus-style local IPC.
3. **COW fork** — current fork is a sync wrapper; true copy-on-write fork needs
   page-table COW support in the L4 memory manager (sits last in section 9.3
   order). Ports that `fork()` heavy address spaces (make, configure) depend
   on this being cheap.
4. **pipe2 flags / O_CLOEXEC / O_NONBLOCK** — verify the flag subset the ring-
   buffer pipe honestly supports and fail-close the rest (follow-up audit).

Each row's promotion from `unsupported`/`partial` to `supported` must land
its real backing AND update P5's `posix_profiles.md` row in the same change,
then this contract's status here — keeping the typed target and the matrix in
lockstep.
