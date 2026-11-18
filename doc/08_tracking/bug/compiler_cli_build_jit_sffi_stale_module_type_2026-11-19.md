# compiler_cli_build HIR failure: jit_sffi.spl stale `Module` import (pinned 41ea2084e43)

Date: 2026-11-19
Host: Windows 11, x86_64-pc-windows-msvc
Lane: criterion-2 full bootstrap attempt #6, pinned source 41ea2084e43b,
authorized run c42full (receipt 5ef58caaf19b…), stage2 slim verification matrix

## Observation

Attempt #6 (re-pin at release head 41ea2084e43, which carries upstream HIR
fixes b981dfbf38b / d0086d14b92 / 16006bb319e) CLEARED the attempt-#5 blocker:
the editor-composite "mismatched qualified declaration" errors in
tui_shell.spl/editor_ctrl_core.spl did not recur, and the stage-2 generation
qualified (`stage2_qualification_status=passed`).

The run then failed later in the same `compiler_cli_build` task, at the very
end of the streaming-HIR phase (3999/4001 modules succeeded):

```
[collect-all] 1 module(s) poisoned, 1 error(s) collected across 6869 source(s)
[collect-all]   poisoned: app.io.jit_sffi
[ERROR]   HIR lowering error in src/app/io/jit_sffi.spl: unresolved type: Module
```

VERDICT ABORTED, stage-engine-failed; downstream PASS rows missing
(compiler_cli_build, compiler_bootstrap_tests, interpreter_interpreter_tests,
loader_interpreter_tests) — same missing-row shape as attempt #5 but a
different, genuine root cause.

## Root cause

`src/app/io/jit_sffi.spl` still imported `compiler.frontend.parser_types.{Module}`
and declared `var modules: Dict<text, Module> = {}` (line 147). The type was
renamed to `struct ParserModule` in parser_types.spl; `Module` no longer
exists there. The stale import went unnoticed because:

- jit_sffi.spl is the ONLY file in src/ importing `parser_types.{Module}`.
- The stage-2 native-build surface (bootstrap closure, 1579 modules) does not
  include app.io.jit_sffi, so stage-2 admission compiled fine.
- The failure only surfaces when the stage-2 compiler builds the full-cli
  closure (4001 modules, slim verification matrix).

Both consumers of the value prove the intended type:
`module_surfaces_from_modules(modules: Dict<text, ParserModule>, …)`
(module_surface_registry.spl:426) and the result of `parse_full_frontend`.

## Fix

`Module` → `ParserModule` at the import (line 24) and the Dict annotation
(line 147) in src/app/io/jit_sffi.spl. Two-line rename; no behavior change.

## Evidence

- c42full scheduler failure manifest:
  `c42full/scheduler/bootstrap-20261118T185243Z-29135/failure-manifest.env`
  (stage2_qualification_status=passed)
- Task log: `c42full/stage2-compiler-tests/x86_64-pc-windows-msvc/verification/logs/compiler_cli_build.log`
  (HIR 3999/4001, single poisoned module app.io.jit_sffi)
