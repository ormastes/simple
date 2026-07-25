# Stage2 rejects multiline boolean return continuations

**Status:** BOOTSTRAP-COMPATIBILITY SOURCE FIXED
**Severity:** P1 — prevents an incremental Stage4 CLI build

## Reproduction

The retained Stage2 v39 driver rejects a function whose implicit return spans
newline-indented `or` continuations, reporting `unexpected token ... Newline`
and `Indent`. The same `cli_is_log_option` source is accepted by newer tooling,
so a full CLI source tree can outrun its retained bootstrap parser.

## Solution

Keep bootstrap-consumed CLI code within the retained parser surface: handle the
three prefix forms with early returns and use the existing array `contains`
operation for exact options. This preserves behavior without adding a helper or
rebuilding the Rust seed. A future admitted Stage2 may remove this compatibility
constraint after directly proving multiline implicit-return continuation.

## Evidence

- Stage4 v43 direct incremental build: reproduced at
  `src/app/cli/_CliMain/main_and_help.spl:101`
- retained-Stage2 parse and current Stage4 rebuild: pending
