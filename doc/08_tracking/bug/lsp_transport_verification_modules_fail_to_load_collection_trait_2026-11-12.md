# LSP transport / verification modules fail to load: `text` vs trait `Collection`

- Date: 2026-11-12
- Status: open
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
