# Bug: `simple lint` fails on any file containing a `class` — "method `get` not found on type `str`"

- **Date:** 2026-07-27
- **Status:** open
- **Severity:** high (lint unusable as a lane gate for class-bearing OS sources)
- **Found by:** two independent SimpleOS harden lanes (P1 IPC, P3 VFS) on untouched control files

## Symptom
`bin/simple lint <file>` (seed binary copy) on ANY `.spl` file that contains a
`class` declaration errors:

```
method `get` not found on type `str` (receiver value: <ClassName>)
```

Reproduced on untouched `src/os/kernel/ipc/capability.spl`,
`src/os/kernel/ipc/l4_fast_ipc.spl`, and a control file under
`src/os/kernel/fs/` — not caused by new lane code.

## Trace
Points into
`src/compiler/90.tools/lint/_LintMain/traceability_and_assertions.spl:495,535` —
a class-name value is flowing into a Dict/`get` call that expects `str`.

## Impact
Lint cannot gate any lane whose sources use classes (most of src/os). Lanes
fell back to spec runs as the quality gate.

## Next step
Fix in pure-Simple lint (`traceability_and_assertions.spl`): guard/convert the
receiver before `.get`, add a regression fixture with a minimal `class` file.
