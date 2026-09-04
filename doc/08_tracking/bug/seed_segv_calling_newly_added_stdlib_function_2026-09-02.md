# Rust seed SEGVs when calling a NEWLY ADDED function in an existing stdlib module

Date: 2026-09-02. Host: Windows 11. Binary: `bin/simple.exe` (Rust bootstrap seed).
Status: OPEN. Blocks: extracting testable pure helpers out of stdlib modules.

## Symptom

Adding a new top-level function to an existing stdlib module and CALLING it
from user code terminates the process with SIGSEGV (rc=139). The crash is at
CALL time, not import time: statements before the call print normally.

Existing functions of the very same module, in the very same run, work.

## Minimal reproduction (measured, rc read into a variable, never via a pipe)

Added to `src/lib/nogc_sync_mut/env/platform.spl` a pure helper extracted from
`detect_os()` with its branches unchanged:

```
fn os_from_uname(sysname: text) -> text:
    if sysname == "Linux": return "linux"
    ...
    "unknown"
```

| probe | body | rc |
|---|---|---|
| p7 (control) | `use std.env.platform.{detect_os, is_linux}` + call both | **0**, prints `windows` / `false` |
| p6 | `use std.env.platform.{detect_os, os_from_uname}` + call both | **139**; prints `a=windows`, then SEGV on the second call |
| p5 | import + call `os_from_uname` only | **139**, no output |

Invariant across all of: `pub fn` vs `fn`; parameter named `uname` vs
`sysname`; with and without adding `platform.os_from_uname` to the
`export platform.…` list in `src/lib/nogc_sync_mut/env/__init__.spl`.

There is no name collision: `/usr/bin/grep -rn os_from_uname src` returned only
the definition, its single call site, and the export line.

## Why it matters

It makes a whole class of safe refactors impossible under the seed: you cannot
extract a pure, testable helper out of a stdlib module, which is exactly what
is needed to make an untestable path (here, the BSD `uname -s` fall-through in
`detect_os()`, unreachable from a Windows host) testable as a pure function.

The workaround taken was to REVERT the extraction and pin the fall-through
structurally instead
(`test/01_unit/lib/platform/host_detection_bsd_fallback_preserved_spec.spl`).
That is a workaround, recorded here rather than normalized silently.

## Not yet established

- Whether the defect is specific to `std.env.platform` or to any stdlib module.
- Whether a redeployed pure-Simple `bin/simple` reproduces it. Only the Rust
  seed was available on this host.

## Related

- `doc/05_design/platform/host_detection/platform_variation_minimization_2026-09-02.md`
