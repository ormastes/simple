# Unused `std.gpu.engine2d.engine` import drops the `print` prelude - 2026-09-16

- **Status:** OPEN (filed 2026-09-16)
- **Severity:** P2 — blocks recorded repros and any engine2d script whose import is unused
- **Lane:** macOS bug/todo db sweep 2026-09-16 — found while re-running `module_load_24s_unless_window_winit_imported_2026-07-25.md`
- **Host:** macOS 25.5.0, Apple M4 (aarch64)
- **Seed:** `bin/simple` → `src/compiler_rust/target/bootstrap/simple` (rebuilt 2026-09-14)

## Symptom

A program that imports `std.gpu.engine2d.engine` without using any of its
bindings fails to compile with:

```
error: semantic: variable 'print' not found
```

Both execution modes are affected (interpreter and JIT). The exact probe
content recorded in `module_load_24s_unless_window_winit_imported_2026-07-25.md`
(two-line `fn main() -> i64: print "ok"; 0` with the engine2d import) is
therefore un-runnable as recorded, from /tmp and from repo-internal scratch
paths alike.

## Reproduction

```sh
# any file like:
#   import std.gpu.engine2d.engine
#   fn main() -> i64: print "ok"; 0
bin/simple run probe.spl        # error: semantic: variable 'print' not found
```

The repo's own `scratchpad/cpu_lane_probe.spl` (which *uses* the import)
parses and runs clean in interpreter mode, so the defect is specifically the
*unused* import path — importing the module without referencing a binding
drops the `print` prelude from scope.

## Context

2026-09-16 sweep re-ran the 2026-07-25 module-load probe to re-measure the
24 s loader tax. The tax itself is gone (see the 2026-09-16 section in that
record — usable-import variants run 1.9–3.0 s), but the exact recorded probe
content cannot run at all because of this defect, so the re-measure had to use
modified probes. Fix this first if the 2026-07-25 record ever needs its exact
repro re-run.

## Suspected area

Frontend import/elision logic: an unused import of a large module is
desugared/elided in a way that also removes the implicit `print` prelude
binding. Compare how the unused-import path differs from the used-import path
for prelude injection (`src/compiler_rust/compiler/src/frontend/`,
interpreter mode reproduced it too, so the seam is above the two backends).

## Acceptance

- A two-line program importing `std.gpu.engine2d.engine` unused and printing
  `"ok"` compiles and prints in both interpreter and JIT modes.
- The 2026-07-25 probe content runs as recorded.
- Regression spec: unused-import program prints in at least interpreter mode.
