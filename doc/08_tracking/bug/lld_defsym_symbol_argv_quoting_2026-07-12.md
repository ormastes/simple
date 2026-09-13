# LLD defsym symbol argv quoting

**Status:** CLOSED-STALE (2026-09-12: no parseable status and no cheap repro in the record; reopen with a fresh repro against the current seed)

ARM64 and RV64 discover the exact generated `spl_start` symbol with `nm`. When
the workspace path contains hyphens, the symbol also contains hyphens and LLD
parses an unquoted `--defsym=spl_start=<symbol>` RHS as subtraction.

Passing literal quotes works when invoking `ld.lld` directly. The focused ARM
command was also mixing overlay source roots with an entry path in the original
tree. That made the entry an external absolute module and produced a symbol
containing the hyphenated workspace path instead of the normal safe module
name.

TODO: rerun with the entry under the same focused overlay root as its sources.
If a correctly rooted module still produces linker-expression punctuation,
then fix identifier mangling or argv preservation at its owner. Do not rename
the discovered symbol, move the workspace, or add a hardcoded alias.

## Triage 2026-09-12

Status line inserted mechanically by the bug-db triage (record had no parseable `Status:` line); rule: filed before 2026-07-29 with no cheap repro → CLOSED-STALE, otherwise OPEN (unverified).
