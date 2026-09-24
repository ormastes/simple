# Windows Stage 2 sanity: collector syscall failure and independent candidate crash

Status: collector fixed and exercised on Windows; candidate remains rejected.

The Stage 2 build compiled and linked 834 files, then its sanity evidence reported
version and unsupported-command status 139 plus frontend status 126. The frontend
driver printed `The syscall function is unimplemented ... line 295`, followed by
a missing frontend log. The collector selected a Linux `renameat2` number from
the CPU architecture, without checking the operating system, and attempted it
through MSYS Perl. Its `/proc/<pid>/fd` output authority also leaked into the
Windows sanity path. This was a host verification failure after collection,
not evidence of a compiler frontend failure.

There was a separate compiler failure. Direct Windows execution of
`build/bootstrap/stage2/x86_64-pc-windows-gnu/simple.exe.rejected --version`
terminated with access violation `0xC0000005` and no output. Candidate SHA-256:
`3e68d8d94ff78bcdaa41ae264cd6f290f9037791215d0a05316434eff2d8c456`.
The collector fix does not admit this binary.

The shared frontend capture facade now selects a Windows host helper that places
a suspended native process in a kill-on-close Job Object before resuming it.
It contains native descendants even when their parent exits, caps only combined
stdout/stderr, and records the exact Windows exit status and the helper hash.
Real output directories are held without delete sharing and reparse points are
rejected. Same-directory temporary files are published with
`MoveFileExW(MOVEFILE_WRITE_THROUGH)` without replacement. Existing evidence is
never overwritten. Linux keeps its existing descriptor-based collector.
Simple compiler/runtime/product dependencies are unchanged by this host helper.

Evidence on 2026-09-08:

- `python test/01_unit/scripts/process_group_bounded_log_windows_test.py`:
  PASS, eight actual Windows cases. Combined streams/nonzero status, native
  descendant timeout, overflow and cleanup, exact NTSTATUS, initial and late
  output collisions, failed assignment before execution, and helper mutation.
  Receipts: `build/native_probe/stage2-sanity-windows/collector-regression-ue0fph6f/`.
- `sh scripts/check/check-stage2-sanity-artifact-binding.shs`: PASS. Candidate
  mutation and deleted, tampered, or legacy frontend evidence are rejected.
- Diagnostic invocation of the canonical `candidate_frontend_smoke` function
  against the preserved rejected candidate: frontend status 139, exact native
  status 3221225477, reason `child-native-exception`, and unchanged candidate SHA.
  Complete log/status/collector evidence:
  `build/native_probe/stage2-sanity-windows/rejected-frontend.470wEo/`.
- Direct Windows version probe:
  `build/native_probe/stage2-sanity-windows/version-direct.json`.

No compiler rebuild, admission, deployment, or push was performed for this fix.
The next action is to diagnose the candidate's native access violation, then run
the canonical sanity/admission path with its existing build cache.

Platform references: Microsoft documents child containment and kill-on-close
in [Job Objects](https://learn.microsoft.com/en-us/windows/win32/procthread/job-objects).
The no-replacement move contract is documented by
[MoveFileExW](https://learn.microsoft.com/en-us/windows/win32/api/winbase/nf-winbase-movefileexw).
