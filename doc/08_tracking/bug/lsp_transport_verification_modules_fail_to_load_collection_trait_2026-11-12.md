# LSP transport / verification modules fail to load: `text` vs trait `Collection`

- Date: 2026-11-12
- Status: verification-pending
- Severity: P2 (blocks every behavioural spec of the LSP diagnostics handler)
- Found by: pub-fn audit lane (work/audit-fixes-20261112)

## Symptom

On the phase-1 Rust seed interpreter, any spec that imports
`std.nogc_sync_mut.lsp.transport` or `std.nogc_sync_mut.lsp.handlers.verification`
(and so `std.nogc_sync_mut.lsp.handlers.diagnostics`, which imports both) runs
zero examples:

```
error: semantic: type `text` does not implement required method `contains` from trait `Collection`; type `text` does not implement required method `count_matching` from trait `Collection`
error: test-runner: no examples executed
SPEC FILE VERDICT: ... outcome=ERROR declared>=1 executed=0
```

`std.nogc_sync_mut.lsp.protocol` and `compiler.treesitter` load fine (bisected
with one-line probe specs).

## Repro

`bin/simple.exe test test/01_unit/app/lsp/diagnostics_portable_subprocess_spec.spl --no-session-daemon`

The spec checks that `collect_compiler_diagnostics` reports a diagnostic
without `/bin/sh`. The `/bin/sh` fix landed with it. The spec stays red
(executed=0) until this load error is fixed.

## Next step

Find the `Collection` bound that `text` is checked against in the transport
or verification import closure. Then add the missing `text` impl, or fix the
bound.

## Fix (2026-11-12)

Root cause: `lsp/transport.spl` had four unused legacy imports (`sys`,
`io.stdio`, `core.json`, `core.string`). `core.string` resolves to the seed's
stale std snapshot (`src/compiler_rust/lib/std/src/core/string_ops.spl`), whose
`impl Collection<char> for text` is empty, so the trait check rejected it.
`verification.spl` failed only because it imports `lsp.transport`. Removed the
unused imports.

Evidence: `diagnostics_portable_subprocess_spec.spl` went from
`outcome=ERROR executed=0` to `outcome=OK executed=1 passed=1 failed=0`.

Latent trap, not fixed here: any module that still does `import core.string`
hits the same error. Other importers: `gc_async_mut/lsp/transport.spl`,
`nogc_async_mut/lsp/transport.spl`, `app/dap/*`, `app/protocol/transport.spl`.
The seed reads the std snapshot from its build tree (p1 worktree), not from the
working checkout, so a fix to `string_ops.spl` can't be checked from a lane.
