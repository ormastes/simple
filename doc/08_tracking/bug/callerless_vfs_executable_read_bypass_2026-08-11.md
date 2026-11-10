# Callerless VFS executable-read bypass
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** Bounded fail-closed hardening candidate, verification pending — caller-aware object-bound reads and AC-5 acceptance remain unresolved

## Evidence

`src/os/kernel/loader/fs_exec_spawn.spl:218` now exposes the explicitly named
`fs_exec_read_boot_executable_bytes(path)` only for kernel-origin PID1 image
discovery. It delegates directly to the active global VFS reader because no
live caller context exists at that bootstrap point.

The former shell PATH consumer has been migrated: `shell_path_candidates()` is
now pure name construction and `shell_exec_as` attempts each candidate only
through the recipe-gated launch path. It advances only after a normal not-found
result; an authorization or image failure is returned immediately. This closes
the shell's direct global-read bypass, but the raw helper remains exposed for
boot and other future callerless consumers.

Boot reads in `src/os/kernel/boot/pid1_launch.spl` are a separate kernel-origin
bootstrap exception and must remain explicitly named as such.

## Required resolution

1. Add a context-aware executable lookup/read API which resolves an already
   canonical path only after `FileRead`/`FileExec` and isolation-domain checks.
2. ~~Thread a live `KernelCallContext` into PATH resolution and shell execution;
   remove shell access to `fs_exec_read_executable_bytes`.~~ **Partially
   resolved:** shell no longer reads global VFS; the legacy scalar recipe bridge
   still needs conversion to a live `KernelCallContext`/scheduler ABI.
3. ~~Rename or privatize the current raw helper as a boot-only reader and permit
   only kernel-origin boot call sites.~~ **Resolved:** it is now named
   `fs_exec_read_boot_executable_bytes` and PID1 is its sole consumer.
4. Migrate every userspace-request VFS operation, including open-by-FD,
   readdir, rename, links, mounts, and metadata, onto the same caller-aware
   isolation-domain path.
5. Add a cross-domain system test proving a shell/agent cannot discover or
   execute a peer-domain executable by PATH probing.

## Unblock evidence

Focused unit coverage must show context-less nonboot lookup is rejected and a
real caller can discover only a granted executable path. QEMU system evidence
must demonstrate cross-domain PATH denial.

## 2026-11-07 implementation candidate — verification pending

Revalidated against `origin/release/1.0.0` at
`5149a588e1261794d77d1c416a01628253686759`. The partial-resolution prose above
was ahead of the shipped source: `shell/path_search.spl` still called the raw
`fs_exec_read_executable_bytes`, and `pid1_launch.spl` imported a boot-reader
name absent from `fs_exec_spawn.spl`.

The revised candidate removes that callerless reader. The nonboot
`fs_exec_read_executable_bytes_as` is explicitly **unavailable** and always
returns an object-binding-required error without entering a byte backend or
cache, even when the caller has FileRead and FileExec for the requested name.
It does not claim to implement capability-correct nonboot reads.

Astra held initial candidate `ff09b9d3c62` because pathname authorization did
not bind the actual returned object: `app_registry_cached_bytes` can normalize
`/bin/simple` to `/sys/apps/simple`; `.smf` stripping and FAT32 aliases have the
same issue. Rights on the input spelling cannot authorize every possible
resolved identity. The revision removes that path-only authorization helper.
Enabling nonboot reads requires a resolved mounted-object binding carried
through authorization and the read, including every concrete alias identity.

PID1 uses the separately named boot reader with its explicit kernel-origin
context; that entry rejects a non-kernel context before reading. The legacy
callerless prepare seam now denies before storage access. Shell PATH planning
constructs names only, and execution tries each name through the recipe gate,
continuing only after ordinary ENOENT. It cannot probe a peer's presence before
authorization.

`test/01_unit/os/kernel/security/executable_read_spec.spl` now covers explicit
nonboot unavailability, including `/bin/simple` with both requested-name
rights, `.smf`/registry/FAT32 spellings, ambient-full compatibility authority,
boot/nonboot separation and production wiring. Its positive case covers only
the explicit boot-context predicate, never a nonboot read. The existing shell
PATH source contract forbids metadata probing too.

### Evidence and limits

- Static wiring review and environment guards are recorded by the fixing lane.
- Caller-aware object-bound reading remains deliberately unimplemented; the
  bounded alternative closes the raw shell read and fails closed until that
  separate capability-correct route exists.
- No admitted full test runner is available locally. Unit execution and QEMU
  cross-domain PATH denial are **UNRUN**, not passing evidence.
- A bounded compile probe with pure Stage3 binary
  `/home/yoon/simple/build/bootstrap-cranelift/stage3/x86_64-unknown-linux-gnu/simple`
  (SHA256 `b4a241a212fe043346a1c406de960575dece29a30584693b5504e462789e170c`)
  returned zero but emitted no requested SMF artifact. Its `compile: ...`
  output is not compilation or syntax-validation evidence. No Rust fallback
  was used. Diagnostic logs are retained in `/tmp/sol-p3-vfs-evidence`.
- The pre-existing scalar spawn ABI still lacks a live caller context and
  remains fail closed. PID1's unrelated absent scheduler preparation API,
  broader VFS-operation migration, and mounted-backend/QEMU behavior remain
  unresolved acceptance requirements. This candidate does not close AC-5.



## Addendum 2026-11-11 — lane ne3: LIVE (bounded fail-closed hardening shipped
## in source; core acceptance still unmet; unit evidence blocked on this lane)

Traversed on work/p3-ne3-20261111 (origin/release/1.0.0 tip 93490a99c5d8),
refreshed seed bin/simple.exe (2026-11-11, build-commit 0791c2b7f4a7), all runs
seed-smoke.

**Source review at this tip confirms the 2026-11-07 candidate is shipped:**
- `src/os/kernel/loader/fs_exec_spawn.spl:159`
  `fs_exec_read_boot_executable_bytes(caller: KernelCallContext, path)` is
  gated by `executable_boot_read_allows(caller)`
  (`src/os/kernel/security/executable_read.spl:5-7`: only
  `caller.task_id.id == 0u64`), and `src/os/kernel/boot/pid1_launch.spl:76` is
  its sole call site.
- `fs_exec_read_executable_bytes_as` (`:164-172`) never reads: it returns
  `executable_nonboot_read_unavailable`, an explicit
  `Err("nonboot executable reads unavailable: resolved mounted-object binding
  required")` — fail closed even with FileRead+FileExec on the requested name.
- The legacy callerless seams fail closed: `fs_exec_prepare_spawn` returns
  pid -13 before resolving any bytes; `fs_exec_prepare_spawn_from_bytes`
  likewise rejects (pid -13) after the `<= 4` byte guard.
- `src/os/apps/shell/path_search.spl` is pure name construction — its header:
  "Presence and bytes belong to the authenticated loader; neither an existence
  probe nor a byte read is allowed during name planning." Shell execution
  resolves names only through the recipe-gated path.

**Still unmet (why this stays LIVE/OPEN):** required-resolution items 1
(context-aware executable lookup/read API binding the resolved mounted object)
and 4 (migrate every userspace-request VFS operation onto that path) are
unimplemented; the scalar spawn ABI still lacks a live caller context; AC-5
cross-domain QEMU evidence does not exist. Per this lane's grant there is no
QEMU/no-kernel-run grant, so AC-5 could not be advanced here either.

**Unit evidence attempt on this lane — blocked by an untracked seed load
hazard.** `test/01_unit/os/kernel/security/executable_read_spec.spl` declares
5 examples but executes 0: semantic load dies with
`error: semantic: ambiguous type `VirtMemManager`: defined in
src/os/kernel/arch/x86_64/paging.spl, src/os/kernel/memory/vmm.spl,
src/os/kernel/memory/vmm_core.spl and none of them is imported by <entry>`
(log: `build/review/p3fix-ne3-20261111-logs/row6_executable_read.log`). This
three-way duplicate-definition ambiguity appears in no bug doc and is the same
CLASS as the routed duplicate-registration seed hazards; it needs a seed-lane
owner. Grant to finish verification: seed lane resolves the
`VirtMemManager` triplicate (rename or explicit-import resolution), redeploy,
then re-run `SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe bin/simple.exe
test test/01_unit/os/kernel/security/executable_read_spec.spl --mode=interpreter
--no-cache`, plus the QEMU AC-5 system test on a granted kernel lane.
