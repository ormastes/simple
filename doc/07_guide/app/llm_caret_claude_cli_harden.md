# LLM Caret Claude CLI Harden Guide

Date: 2026-07-24

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

## Production Caret Wrapper

`bin/caret` launches a cached native Caret artifact. It checks, in order:

1. `SIMPLE_CARET_NATIVE` when explicitly set;
2. `build/bootstrap/caret-package/caret`;
3. target-specific `bin/release/<target>/caret`;
4. target-specific `build/bootstrap/full/<target>/caret`.

The wrapper fails with exit 127 when no cached artifact exists or an explicit
override is not executable. For a deliberate source-debug session only, set
`SIMPLE_CARET_ALLOW_SOURCE_FALLBACK=1`; production and acceptance runs must not
use that fallback.

Build the cached artifact with the pure self-hosted runtime:

```bash
bin/simple native-build \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/llm_caret/main.spl --strip \
  --output build/bootstrap/caret-package/caret
```

The deterministic process contract is
`test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl`.
It uses an explicit executable override to test selection and forwarding
without claiming that the release artifact was built.
