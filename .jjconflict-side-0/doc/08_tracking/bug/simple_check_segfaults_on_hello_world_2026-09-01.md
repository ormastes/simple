# `simple check` SEGVs on a two-line hello world

**Date:** 2026-09-01
**Status:** OPEN — measured, not fixed
**Severity:** the fast syntax gate is unusable; `run` is unaffected

## Reproduction

```
$ printf 'fn main():\n    print "ok"\n' > /tmp/ok.spl

$ src/compiler_rust/target/release/simple.exe check /tmp/ok.spl ; rc=$?
Segmentation fault
rc=139

$ src/compiler_rust/target/release/simple.exe run /tmp/ok.spl ; rc=$?
ok
rc=0
```

Binary: fresh seed built from current `src/compiler_rust`, 38,711,808 bytes.
Host: Windows / MSYS2. Exit status read directly into a variable, not through
a pipe.

## Why it matters

`check` is the cheap "does this file still parse" gate. With it crashing on
ANY input, the natural quick validation step is unavailable, and its failure
mode is indistinguishable from "your file is broken" — it returns 139
regardless of the input. This session hit exactly that: two edited compiler
files were run through `check`, both returned 139, and it took a control run
on a trivial file to establish the files were fine and the COMMAND was broken.

Anyone using `check` as a pre-commit or CI gate on this binary would read a
uniform crash as a source defect.

## Not the same as the other SEGVs fixed today

- Stage 2's parse SEGV was module init never running on MSVC (fixed).
- The struct-receiver probe SEGV was `/FORCE:MULTIPLE,UNRESOLVED` putting the
  CRT entry at address 0 (fixed).
Both were in natively-built artifacts. This one is the SEED ITSELF crashing on
a code path (`check`) that `run` does not take, so it is a third, distinct
site.

## Suggested next step

Get a stack. `cdb.exe` is available under the Windows SDK
(`C:\Program Files (x86)\Windows Kits\10\Debuggers\x64\cdb.exe`) and was used
successfully on this chain today. Compare the `check` entry path against
`run`'s in the CLI dispatch table — `check` is one of the commands absent from
`--help` output, so it may be a less-exercised route.

## Unix impact

Unknown — reproduced only on Windows. Worth checking whether `check` crashes
on Linux/macOS too before assuming it is platform-specific; nothing in the
symptom suggests a Windows-only cause.
