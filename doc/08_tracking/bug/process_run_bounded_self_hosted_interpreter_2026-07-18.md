# `process_run_bounded` rejected by deployed self-hosted interpreter

Date: 2026-07-18

## Reproduction

Import `app.io.mod.{process_run_bounded}` from an interpreter-tested app module
and execute its focused SSpec through `bin/simple test ... --mode=interpreter
--no-session-daemon`.

Observed terminal error:

```text
error: semantic: unknown extern function: rt_process_run_bounded
```

The symbol exists in the Rust interpreter registry, C runtime, runtime header,
stage-4 closure, and native lowering. The deployed pure-Simple interpreter path
does not expose it consistently. `rt_process_run_timeout` is adjacent and should
be audited at the same boundary.

## Impact

App code can use the direct-argv `process_run` facade, but cannot enforce a
pre-capture byte bound in interpreter-tested closures. LLM Caret infrastructure
access therefore streams object/attachment payloads to provider file/stdin
operands and caps captured diagnostics after `process_run`; this avoids payload
buffering but is not equivalent to an OS-level capture bound.

## Acceptance

- The self-hosted interpreter resolves `rt_process_run_bounded` through the
  canonical `app.io.mod` facade.
- `test/01_unit/app/test_runner_bounded_output_contract_spec.spl` and the LLM
  Caret infrastructure focused specs pass in interpreter mode.
- Large child output is killed/capped before unbounded allocation.

## Revived-lane status (2026-07-18)

Current `origin/main` source contains the `app.io.mod` re-export, the
`process_run_bounded` facade, Rust interpreter registration, C runtime owner,
native tuple lowering, and Stage-4 symbol closure. The recovered Caret lane now
uses that facade at its single production runner seam.

Runtime acceptance remains blocked: a fresh canonical bootstrap passed Stage 3,
then the full-CLI Stage 4 was terminated by SIGTERM (exit 143) while compiling
`main.spl`. No bootstrap-only seed was substituted and no build retry was made.
