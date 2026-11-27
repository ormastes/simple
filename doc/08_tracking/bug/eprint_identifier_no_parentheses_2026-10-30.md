# Identifier argument to bare eprint is not parsed as a call

Status: grammar gap open; runner caller repair rebuilt and started; MC/DC error branch unverified.

The native runner build from `e01669c` plus the owned runner fixes failed in
`src/app/test_runner_new/test_runner_main.spl` at `eprint mcdc_line` in the
MC/DC failure-reporting branch. The diagnostic named undefined variable
`eprint`; dependent MIR failures followed. This is not evidence that MC/DC
execution itself failed: the runner executable had not been built.

Minimal reproduction:

```simple
fn warn(message: text):
    eprint message
```

`parser_stmts.spl` gives `print` a dedicated bare-argument branch. Its generic
`try_parse_bare_ident_string_call` only accepts a string-literal next token.
An identifier argument therefore does not become a call. The earlier
`lint_parse001_false_positive_on_spec_files_2026-07-29.md` tracks the related
string-led DSL implementation, not support for arbitrary argument expressions.

The focused caller repair is `eprint(mcdc_line)`. It retains the existing
stderr-plus-newline builtin and does not send diagnostics into the stdout
result protocol. No parser or producer change is included. The grammar gap
remains open; this explicit call is not a claim that the compact form works.

Existing regression: `test/01_unit/compiler/hir/eprint_builtin_native_path_spec.spl`
already lowers `eprint(msg)` beside `print(msg)` with zero diagnostics and
checks an unknown-callee negative control. Do not duplicate that unit case.

Required execution evidence: rebuild the actual runner with the same admitted
producer, preserving source-refresh authority; require the previously failing
module and its dependent MIR closure to complete. Separately exercise the
MC/DC error-reporting branch and verify diagnostics remain on stderr with a
nonpassing result. The user-requested MC/DC-off smoke does not exercise that
error branch and must not be represented as its verification.

Build evidence (2026-10-30): the parent runner lane rebuilt and started
`build/runner-goal-logs/native-runner-e01669c-owned26/simple_test_runner.exe`.
SHA-256: `E101710A6CCD629E5C77F42B962729D6EE33CED6B100E77B6EFC8AB329E8DE9C`.
This artifact includes other runner-lane changes; it establishes that the
previous eprint MIR blocker no longer prevents linking/startup, not an isolated
unit-test pass. MC/DC was off. Neither the existing HIR spec nor the MC/DC
error-reporting branch was executed as part of this repair's validation.
