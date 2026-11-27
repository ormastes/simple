# Windows stdin command native acceptance inventory

Status: **NOT_COVERED / NOT_RUN**. This manual contains acceptance requirements,
not a fabricated executable success fixture. The bounded Windows native
campaign is closed for this source-only lane.

Required actual setup: admitted Win64 compiler/runtime, exact SHA256-pinned
controlled stdin producer, protected Host identity store with actual key and
known-host file admission, and genuine Windows process/pipe fault fixtures.

Native qualification must exercise:

- Binary framed stdin at 2105360 bytes while the child also fills stdout and
  stderr; verify exact input completion, actual stdin EOF, independent capture
  limits and both output EOF facts without deadlock.
- Queued/partial stdin completion and cancellation before/after each native
  acquisition, including pending ConnectNamedPipe and pending WriteFile.
- Failed CancelIoEx, GetOverlappedResult, CloseHandle, HeapFree, LocalFree and
  CNG releases; every remaining resource must retain the actual owner.
- Exact image hash mismatch, reparse ancestors, parent replacement attempts,
  existing writer sharing conflicts and same-path executable replacement while
  the real pin remains held through process reaping.
- DOS drive/SUBST remapping between root resolution, hash and process creation;
  verify the same OS-resolved GLOBALROOT volume path is used for every later
  open, application name, argv0 and cwd. Rebinding a selected root must fail
  its original volume/file-ID comparison; include every SUBST suffix ancestor.
- CSPRNG private pipe name, first-instance creation, protected owner/SYSTEM
  DACL, remote-client refusal and exact connected parent-client process ID.
- Startup handle whitelist, suspended admission and expiry immediately before
  CreateProcessW and ResumeThread. Expiry is not the running timeout.
- Actual leader signaled plus empty JobObject, timeout/cancel termination,
  output truncation and copied/stale-owner rejection.
- Authenticated SSH integration: retain the actual protected identity-store
  owner; derive admitted key/known-host paths from its opaque API; require exact
  path equality, strict host checking and the pinned SSH executable digest.

Before framed response decode, the authenticated caller must require no error,
matching executable digest, all input written, actual stdin closure, both output
EOFs, no truncation, actual reaping and confirmed cleanup. A completed pipe write
is a local byte-transfer fact, not proof of a remote task effect.

No POSIX permission-mode fallback qualifies Windows credential admission. No
saved PID, decoded path, caller Boolean or recorded digest adopts a process.
