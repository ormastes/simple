# Self-hosted parser: block lambda as call argument with dedented closing paren fails

**Date:** 2026-07-11 · **Status:** OPEN — divergence reproduced against current source.
**Found:** `simple check` delegation chain investigation. The check worker, when forced
in-process (loop-guard env inherited), fails to parse
`src/app/interpreter/async_runtime/mailbox.spl:525` with
`expected ), got BoolLit 'false'` — the file is in `src/app/check/main.spl`'s import
closure, so the worker dies before it can check anything, and `check` grinds until its
300s timeout.

## Failing construct (real site: `src/app/interpreter/async_runtime/mailbox.spl:522-528`)

```spl
self.high_queue = self.high_queue.filter(\msg:
    if msg.is_stale(max_age_ms):
        dropped = dropped + 1
        false
    else:
        true
)
```

Self-hosted parser: `expected ), got BoolLit 'false'` (then cascades:
`unexpected token in expression: : ':'`, `unexpected token in expression: ) ')'`).
The Rust seed parses the same construct fine. Same pattern repeats at
mailbox.spl:530-536 and :538-544 (`normal_queue`, `low_queue`).

## Minimal repro (`/tmp/repro_block_lambda.spl`)

```spl
# Minimal repro: block lambda as call argument with dedented closing paren.
# Mirrors src/app/interpreter/async_runtime/mailbox.spl:522-528.
fn main():
    val xs = [1, 2, 3]
    var dropped = 0
    val kept = xs.filter(\x:
        if x > 1:
            dropped = dropped + 1
            false
        else:
            true
    )
    print("kept={kept.len()} dropped={dropped}")

main()
```

## Divergence (both parsers verified 2026-07-11)

- **Rust seed accepts:** `bin/release/aarch64-apple-darwin/simple_seed run
  /tmp/repro_block_lambda.spl` → parses, runs, prints `kept=0 dropped=0`, exit 0.
- **Self-hosted parser rejects:** driving `src/compiler/10.frontend/core/parser.spl`
  via the check app (`bin/release/aarch64-apple-darwin/simple_seed run
  src/app/check/main.spl /tmp/repro_block_lambda.spl`) →
  ```
  [parser_error] path /tmp/repro_block_lambda.spl line 9:13: expected ), got BoolLit 'false'
  [parser_error] line 10:13: unexpected token in expression: : ':'
  [parser_error] line 12:5: unexpected token in expression: ) ')'
  /tmp/repro_block_lambda.spl: check failed
  ```
  (Note: the stage-4 binary deployed 2026-07-11 20:23 delegates `run` to the seed
  sibling regardless of `SIMPLE_FRONTEND_DELEGATED`, so the check-app route above is
  the reliable way to exercise the self-hosted parser on a single file.)

The self-hosted parser parses the lambda body as a single inline expression: after the
`if <cond>:` arm it expects the call's `)` immediately, so the block-statement arm body
(`dropped = dropped + 1` newline `false`) breaks it at the first standalone literal. The
seed treats `\x:` followed by an indented block as a block lambda and keeps consuming
statements until the dedented `)` closes the call.

## Impact

- Blocks in-process `check`/`run` of anything whose import closure includes
  `app.interpreter` (the check app itself does — this is what made `simple check` hang
  for 300s per worker when the loop guard leaked into the worker env).
- Will block stage-4 native-build discovery if such code enters the bootstrap closure —
  same failure class as `self_hosted_parser_dedent_continuation_2026-07-11.md`, but this
  one is live (not deploy lag): the divergence reproduces against current
  `src/compiler/10.frontend` source.

## Required fix

Self-hosted parser must accept block lambdas as call arguments: `\param:` followed by an
INDENTed statement block (if/else arms, assignments, trailing expression) inside a call's
parentheses, terminated by the dedented closing `)` — mirroring the seed grammar.
Owner: compiler 10.frontend parser layer. Do NOT normalize the mailbox.spl call sites as
a workaround; the construct is legal per the seed grammar and is idiomatic for
filter/map with stateful bodies.

## Verification (2026-07-16)

Still reproduces at origin tip 8932fcb3a148: `probe09_block_lambda_a.spl` (doc's exact minimal repro). Self-hosted parser via native-build: `[parser_error] line 8:13: expected ), got BoolLit 'false'` then cascading errors, exit 1, no binary produced. Matches documented divergence from seed grammar exactly.
