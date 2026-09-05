# `bin/simple check` emits raw legacy parser-error text instead of the stable `error[Exxxx]` diagnostic format (10/10 examples fail)

- **Date:** 2026-07-20
- **Status:** open
- **Area:** CLI `check` diagnostics pipeline (compiler-facing, likely
  `src/app/*` check-command driver and/or `src/compiler/**` diagnostic
  emission)

## Symptom

`test/02_integration/app/diagnostics/check_diagnostics_contract_spec.spl`
invokes the real deployed binary as a subprocess
(`rt_process_run(SIMPLE_BIN, ["check", <fixture>.spl])`) and asserts on the
current "stable" diagnostics contract: `error[Exxxx]`/`warning[Wxxxx]` codes,
`expected:`/`found:` lines, `= help: ...` hint text, and JSON
`{"status": ...}` summaries. All 10 examples fail — the actual CLI output
does not match this contract at all, for every fixture kind tried (parse
error, type mismatch, return-type mismatch, unresolved-import warning,
missing file).

## Concrete example (parse-error fixture)

Fixture (`seed_invalid_source()`): `"fn main():\n    val x =\n"`

Expected (spec, `it "prints stable parse code and help in text output"`):
```
error[E0002]
... unexpected token ...
expected: expression
found:    Dedent
= help: try adding `expression` before this token
```
exit code `1`.

Actual (`bin/release/x86_64-unknown-linux-gnu/simple check <fixture>`):
```
[parser_error] line 3:1: unexpected token in expression: Dedent ''
[parser_error_ctx] path /tmp/simple_check_diagnostics_contract_parse.spl kind 182 text ''
<fixture>: check failed
1 error(s) found in 1 of 1 file(s)
```

This is a structurally different, older/raw diagnostic format
(`[parser_error] line L:C: ...` / `[parser_error_ctx] ...`) — no `error[Exxxx]`
code, no `expected:`/`found:` pretty-print, no `= help:` hint line. The other
9 examples (type-mismatch, return-mismatch, unresolved-import warning,
missing-file) show the same pattern: either the expected stable-format
substrings are absent, or the summary status (`All checks passed` vs actual
error text, `true`/`false` warning flags) diverges from the contract.

## Command

```
SIMPLE_RUST_SEED_WARNING=0 timeout 40 bin/release/x86_64-unknown-linux-gnu/simple test test/02_integration/app/diagnostics/check_diagnostics_contract_spec.spl --no-session-daemon
```

Manual repro:
```
printf 'fn main():\n    val x =\n' > /tmp/repro_parse.spl
bin/release/x86_64-unknown-linux-gnu/simple check /tmp/repro_parse.spl
```

## Root-cause hypothesis

The `check` subcommand's parser-error path is emitting via an older/raw
diagnostic formatter (`[parser_error]` / `[parser_error_ctx]` tags) rather
than routing through whatever pipeline produces the `error[Exxxx]` +
`expected:`/`found:` + `= help:` stable format the rest of the compiler's
diagnostics use elsewhere (this pretty format is clearly implemented
somewhere, since the spec was presumably written against real prior output).
Either: (a) the stable-diagnostics formatter regressed/was never wired into
the `check` CLI's parse-error branch specifically, while other error kinds
(type-mismatch, etc.) may or may not be wired correctly (unverified per-kind
— all 10 examples failed but for possibly different reasons), or (b) this
spec was written aspirationally against a diagnostics-format redesign that
was never completed/landed.

## Not attempted

Not a spec-level fix — this is a real CLI/diagnostics-output contract gap
spanning parse errors, type errors, return-type errors, and warnings alike.
No src/** change attempted (compiler diagnostics formatting, out of scope for
a test-triage pass; would need per-diagnostic-kind investigation of
`src/app/**` check-command code and `src/compiler/**` diagnostic emission to
confirm whether the stable format exists anywhere in current source or needs
building from scratch).
