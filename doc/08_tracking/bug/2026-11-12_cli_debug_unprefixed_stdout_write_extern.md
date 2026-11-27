# `cli_debug` modules declare unprefixed `stdout_write` extern that no runtime implements

- **Date:** 2026-11-12
- **Status:** OPEN (same defect class fixed in `src/app/proton_session_plan/main.spl` by work/product-queue-p1-20261112)
- **Severity:** Medium — every path through these modules fails at runtime with "extern backed by no implementation"
- **Area:** `src/app/cli_debug/format.spl:4`, `src/app/cli_debug/main.spl:16`,
  `src/app/cli_debug/_DebugCommands/command_dispatch.spl:6`,
  `src/app/cli_debug/_DebugCommands/session_and_backend.spl:6`

## Summary

The C runtime exports `rt_stdout_write_text(const char* s)` (text writer) and
`rt_stdout_write(int64_t tagged RuntimeValue)`; the established Simple
convention is:

```simple
extern fn rt_stdout_write_text(s: text)
```

(see `src/app/scv/main.spl:49`, `src/app/md_lsp/md_lsp_main.spl:13`).

Four `cli_debug` modules instead declare:

```simple
extern fn stdout_write(s: text)
```

There is no `stdout_write` runtime symbol (the registry carries
`rt_stdout_write`/`rt_stdout_write_text`), so any execution path that calls it
dies with:

```
error: extern `stdout_write` (argc=1) is declared in Simple but backed by no
implementation; refusing to substitute nil for an unresolved extern.
```

## Repro (on the fixed sibling, showing the failure mode)

Before the proton fix, `src/app/proton_session_plan/main.spl` declared the
same unprefixed extern and failed identically:

```bash
./bin/simple.exe run src/app/proton_session_plan/main.spl
# → rt_interp_call: function not found: stdout_write ... E3008
```

## Fix direction

Rename the four declarations (and their call sites) to
`rt_stdout_write_text`, matching the scv/md_lsp convention and the
proton_session_plan fix. Verify by running
`./bin/simple.exe run src/app/cli_debug/main.spl --help` (currently exits 1
through the unresolved extern).
