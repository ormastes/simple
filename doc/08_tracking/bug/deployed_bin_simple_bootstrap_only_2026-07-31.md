# Deployed `bin/simple` is a bootstrap-only binary: no `test`/`run`/`lint`, and cannot parse `@extern`

- **Date:** 2026-07-31
- **Severity:** blocker (no test runner on this machine)
- **Component:** deploy / bootstrap binary
- **Status:** open

## Summary

`bin/release/x86_64-unknown-linux-gnu/simple` was replaced at 12:14 on
2026-07-31 with a **bootstrap-only** build. It reports itself as
`simple-bootstrap 1.0.0-beta` and exposes only `compile`. Every other
subcommand is gone, so nothing on this machine can run specs.

Two independent defects, both reproduced directly:

### 1. Full CLI is missing

```
$ bin/simple test --help
error: unknown command 'test'
```

`run` and `lint` are gone the same way. No rollback target exists on disk —
the previous binary was overwritten in place, not rotated.

Consequence worth calling out: a spec invocation under this binary produces a
one-line `NO_RESULTS` log, which is **indistinguishable from a hang** unless
you read the log body. Five runs were misread as timeouts before the cause was
found. Anything reporting `NO_RESULTS(1L)` on this machine should be assumed to
be this bug until `bin/simple test --help` succeeds.

### 2. `compile` cannot parse a bodiless `@extern fn`

`compile --format=smf` is the only working subcommand, and it rejects the
`@extern` declaration form used throughout `src/lib/`. Four-line repro:

```simple
fn main():
    print("hi")

@extern fn _cos(x: f64) -> f64
```

```
[parser_error] line 5:1: expected :, got EOF ''
[ERROR] phase 4 FAILED
```

The parser is treating `@extern fn` as an ordinary `fn` and demanding a `:`
body. Any module that transitively imports one — e.g. anything reaching
`src/lib/gc_async_mut/game2d/transform.spl`, which is byte-identical to
`origin/main` — fails to compile for this reason alone and not because of
anything in the module under test.

Some inputs additionally crash the compiler outright with
`runtime error: field access on nil receiver` and exit 132 (SIGILL).

## Impact

There is no working verification gate on this machine. `compile` is usable only
for modules with no `@extern` anywhere in their import closure, which excludes
most of `src/lib/`.

## Repro

```bash
bin/simple --version          # simple-bootstrap 1.0.0-beta
bin/simple test --help        # error: unknown command 'test'
printf 'fn main():\n    print("hi")\n\n@extern fn _cos(x: f64) -> f64\n' > /tmp/p.spl
bin/simple compile --format=smf -o /tmp/p.smf /tmp/p.spl   # parser_error
```

## Fix

Redeploy a full-CLI self-hosted binary. A `--full-bootstrap` was in flight in
`simple_release_beta2_wt` — coordinate rather than racing it. **Verify with
`bin/simple test --help` before trusting any spec result**, and re-check the
`@extern` repro above, since a binary that passes the first check can still
carry the second defect.

Deploys should rotate the previous binary aside instead of overwriting in
place, so a broken deploy has a rollback target.
