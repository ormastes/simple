## MCP Wrapper Audit

Date: 2026-04-18
Scope: `bin/simple verify` wrapper and entry routing

STATUS: PASS

Wrapper surface checked:
- `bin/simple verify --help`
- `bin/simple verify --lean-status`
- `bin/simple verify --no-write-report`

Observed command contract:
- `simple verify [options] [file ...]`
- `--lean-status` routes to the Lean status report path
- non-lean invocations route to the full production-readiness verification path
- `--files=a,b,c` and positional file arguments are accepted by the full verify path

Entry routing audited:
- [`src/app/verify/main.spl`](/home/ormastes/dev/pub/simple/src/app/verify/main.spl) is the single CLI entry
- `main()` dispatches `--lean-status` to `run_lean_status(args)`
- all other verify invocations dispatch to `run_full_verify(args)` imported from [`src/app/verify/full_verify.spl`](/home/ormastes/dev/pub/simple/src/app/verify/full_verify.spl)

Wrapper result:
- help output is stable and matches the implemented flags
- lean-status execution is successful
- full verify no longer fails on import or symbol-resolution errors
- current nonzero exit from full verify is a verification result, not a wrapper/runtime crash
