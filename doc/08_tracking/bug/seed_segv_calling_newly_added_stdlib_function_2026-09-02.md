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


## Triage 2026-11-10 (p3-lib2 lane, work/p3-lib2-20261110)

**Verdict: SUPERSEDED — the rc=139 call-time SEGV no longer reproduces on the
origin/release/1.0.0 base with the worktree Rust seed (bin/simple.exe,
built 2026-11-10). Fail-closed or correct on every probe variant.**

Reproduction of the doc's exact scenario (extract `os_from_uname` from
`detect_os` into an existing stdlib module, call it from user code):

- p5/p6 equivalent (`use std.env.platform.{detect_os, os_from_uname}`, call both):
  **rc=0**, both calls return correct values (`windows` / `linux`). No SEGV.
- Control (existing functions only): rc=0, as before.
- Missing-function variant (helper added to the `nogc_sync_mut` family copy
  while `std.env.platform` resolves to the `nogc_async_mut` copy): the seed now
  fails CLOSED with `use-warning` + `error[E1002]: function 'os_from_uname' not
  found`, **rc=1** — no crash, no silent wrong-module dispatch.
- Architecture note for future reproducers: `std.env.platform` resolves to
  `src/lib/nogc_async_mut/env/platform.spl`; the `nogc_sync_mut` copy is a
  separate module. Edits must land in the module the import actually resolves
  to (per `seed_stdlib_resolves_build_time_repo_root_before_cwd_2026-08-24`,
  cwd-first resolution makes that the invoking tree's copy).
- All probe stdlib edits were reverted; tree clean.

The class of safe refactor the doc wanted (extract pure helpers from stdlib
modules) is no longer blocked on this host. A spec-level regression cannot be
written for this: the repro inherently edits a stdlib module, which an in-tree
`.spl` spec cannot do; the reproduction transcript above is the evidence.

## 2026-11-11 status — SUPERSEDED (P3-essential library lane, work/p3-lib3-20261111)

Reproduced the doc's exact scenario on this lane's refreshed seed
(bin/simple.exe, build-commit `0791c2b7f4a7`, 2026-11-11): extracted
`os_from_uname` into the module `std.env.platform` actually resolves to
(`src/lib/nogc_async_mut/env/platform.spl`) and called it from user code.
p6 equivalent (call `detect_os` + `os_from_uname`): rc=0, prints
`a=windows` / `b=linux`; p5 equivalent (`os_from_uname` alone): rc=0,
prints `b=freebsd`. No SEGV, no rc=139 on either variant. The stdlib edit
was reverted; `git diff -- src/lib` is empty. The rc=139 call-time crash
stays fixed; verified-good boundary is the refreshed seed dispatch itself
(prior verdict recorded at `1fc7d13bc89e`).
