# Windows: `simple test <directory>` fails entirely — test daemon import chain hits an unmaterialized git symlink

**Status:** OPEN
**Filed:** 2026-09-01
**Found by:** triage of `test/01_unit/lib/std/` failures on Windows.

## Symptom

```bash
B=src/compiler_rust/target/release/simple.exe
SIMPLE_BINARY="$B" "$B" test test/01_unit/lib/std/
```

fails immediately with:

```
error: compile failed: parse: in
"\\?\C:\Users\ormas\dev\simple\src\app\debug\coordinator.spl":
Unexpected token: expected expression, found Slash
```

before executing a single spec — no `Results:` line, nothing runnable.
Per-file invocation (`"$B" test <one-spec-file>`) works fine, so this only
affects directory-mode / whole-area runs.

## Root cause

`src/app/debug/coordinator.spl` is a git symlink (mode `120000`) pointing at
`../../lib/nogc_sync_mut/debug/coordinator.spl`:

```bash
git ls-files -s src/app/debug/coordinator.spl
# 120000 e7c682d2084ad51579fe4c57492492d1824cdae4 0	src/app/debug/coordinator.spl
git config core.symlinks
# false
```

With `core.symlinks=false` (the default on this Windows checkout), git
checks the symlink out as a **plain text file containing the link target
string** (`../../lib/nogc_sync_mut/debug/coordinator.spl`, 45 bytes, no
newline) instead of a real symlink or the target's content. When the test
daemon's own module graph (`src/app/test_daemon/__init__.spl` ->
... -> `src/app/debug/coordinator.spl`) is compiled as part of directory-mode
test discovery, the compiler tries to parse that 45-byte path string as
Simple source and chokes on the first `/`.

This is not specific to `test/01_unit/lib/std/` — any directory-mode test
run that pulls in the test daemon's import graph on a `core.symlinks=false`
Windows checkout hits the same wall. The repo has **91 tracked git symlinks**
total (`git ls-files -s | awk '$1==120000'`), so any other module reachable
through one of those 91 paths would fail the same way if imported.

## Why not fixed here

This is an environment/checkout configuration issue (`core.symlinks=false`),
not a defect in `test/01_unit/lib/std/` or in stdlib product code. Per
CLAUDE.md's git safety protocol, changing git config is out of scope for
this task. The workaround used for this triage pass was running every spec
file individually (`"$B" test <file>`) rather than by directory, which
avoids compiling the test daemon's broader import graph.

## Suggested fix directions (not attempted here)

- Enable `core.symlinks=true` and re-checkout on Windows dev machines (needs
  Developer Mode or admin, and a `git checkout -- .` after enabling).
- Or: have the compiler's module loader detect a checked-out git-symlink
  placeholder (small file whose entire content is a relative path with no
  Simple-syntax markers) and follow it, so the tree keeps working the same
  under both `core.symlinks` settings.
- Or: stop using git symlinks for module files reachable by the test daemon
  import graph specifically.

## Repro

```bash
B=src/compiler_rust/target/release/simple.exe
SIMPLE_BINARY="$B" "$B" test test/01_unit/lib/std/ 2>&1 | tail -5
```
