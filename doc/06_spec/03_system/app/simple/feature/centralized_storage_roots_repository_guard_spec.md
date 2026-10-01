# Centralized Storage Roots Repository Guard

The repository guard rejects newly added production code that creates an ambient third storage authority.

## Enforced classes

- direct `/tmp` and `/private/tmp` literals;
- direct reads of `TMPDIR`, `TMP`, `TEMP`, `HOME`, and XDG storage variables;
- `mktemp` outside the central owner;
- new literal cache, build, target, or temporary roots outside central projections.

Normal `--working`, `--staged`, and `--changed-from` modes inspect added lines, so historical migration debt does not block unrelated changes. `--all` is available for migration census. Tests, fixtures, vendored/generated sources, and the two reviewed storage-root owner modules are excluded.

The focused shell test creates an isolated repository, proves working and staged violations fail, proves a central projection passes, and mutates the detector to demonstrate that its self-test bites.
