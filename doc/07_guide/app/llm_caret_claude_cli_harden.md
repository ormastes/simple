# LLM Caret Claude CLI Harden Guide

Date: 2026-07-05

## Trace Gate

Use this gate when changing `src/app/llm_caret` provider files or updating the
Claude CLI migration map:

```bash
sh scripts/check/check-llm-caret-claude-cli-trace.shs
bin/simple test test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl --mode=interpreter
bin/simple spipe-docgen test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl --output doc/06_spec --no-index
```

## Contract

- Every `src/app/llm_caret/*.spl` file needs a source mapping row.
- At least 80% of files and 80% of LOC must be mapped.
- Every current `fn`, `struct`, and `extern fn` symbol needs a backticked
  `kind:name` token in the Simple Symbol Trace table.
- Simple-only providers are allowed when the row names the Simple-only role.
- Live Claude credentials, OAuth, remote control, and terminal UI parity are
  outside this offline trace gate.
