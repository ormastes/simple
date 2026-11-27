# Native SCV history operator scenarios

Status: hand-authored companion; generator and runtime evidence **NOT_RUN**.
Executable source:
`test/03_system/app/scv/feature/scv_native_history_spec.spl`.
Set `SIMPLE_SCV_TEST_RUNTIME` to an absolute admitted pure-Simple runtime path.

1. Snapshot a file twice and inspect `change-log`. Both revision rows must
   carry the same logical change ID and the record must be open. Close the
   change, restore the first operation, and start a new change. Inspect the
   old change explicitly: it remains closed, its latest remains the second
   revision outside current ancestry, and both prior snapshots remain visible.
   Current `change-log` selects the distinct new open change. Default `log`
   still prints one legacy commit row. (REQ-SCV-HISTORY-002)
2. Create two sibling snapshots editing the same line. Merge them through
   native SCV and require one conflict. Set a bookmark and inspect
   `log --all-parents merged`: exact order is merge, left, base, right, with
   the shared base appearing once. Remove the second parent object and repeat:
   the command must return nonzero, identify the unreadable parent, and print
   no partial commit rows. (REQ-SCV-HISTORY-001, REQ-SCV-HISTORY-003)
3. Invoke an absent bookmark and excess history arguments. Every command must
   return nonzero. (REQ-SCV-HISTORY-003)

These scenarios do not certify restore crash safety, packed-object support,
immutable rewrite evolution, or repository-wide read isolation. The native
integration spec adds corruption and resource-bound assertions. No runtime
PASS, coverage percentage, generated-manual quality score, or production
readiness is inferred from this companion.
