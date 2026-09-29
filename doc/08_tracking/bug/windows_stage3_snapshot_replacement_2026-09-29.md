# Windows Stage3 snapshot publication refuses an existing snapshot

The admitted Stage2 `git-state-before.env` is a required immutable input to
Stage3 verification. After verifying it, the materialized-link consumer also
publishes a fresh snapshot at that same path. `File.Move` refused the existing
file, so canonical Windows Stage3 stopped before compilation. Deleting that
input before resuming would invalidate admission and is not a repair.

The Windows consumer now renames its held, validated regular result file with
`SetFileInformationByHandle(FileRenameInfo)`. An existing regular, single-link
destination is atomically replaced on the same volume; an absent destination
uses non-replacing rename. Parent handles remain held without write/delete
sharing. Directories, reparse points, hardlinks and cross-volume publication
are refused. Validation or kernel rename failure preserves the prior output.
This is mutable-name replacement, not a compare-and-swap identity guarantee.
The existing private-result write-then-open behavior is unchanged. Unix
publication retains its existing rename behavior.

## Focused evidence

The regression script extracts the actual embedded consumer, tests its
publisher, then uses a tiny real Git checkout and the canonical Windows
materializer to generate a real receipt. It does not fabricate admission.

- Cycle1: absent and existing publication, locked-destination failure,
  hardlink/directory/reparse refusal and cross-volume preservation passed.
- The first complete-consumer fixture stopped before publication because its
  test environment had mixed Windows separators and lacked MSYS tools in
  PATH. Only the fixture was corrected; the production patch was unchanged.
- Cycle2 ran only that failed criterion: first publication, repeated
  publication and invalid-receipt preservation passed, raw exit0.

Evidence is preserved at
`D:/dev/simple-windows-reviewed-bootstrap-20260929/snapshot-publisher-fix-20260929/{cycle1,cycle2}`.
The cycle2 `result.env` records the consumer result. No full bootstrap PASS is
claimed by this focused regression.

Run the complete regression on Windows with a fresh D evidence directory:

```powershell
powershell.exe -NoProfile -ExecutionPolicy Bypass -File scripts/check/check-stage3-snapshot-publication-windows.ps1 -EvidenceRoot D:/dev/snapshot-publication-test
```

`-ConsumerOnly` is for retrying the consumer fixture without repeating already
passed direct publication checks.
