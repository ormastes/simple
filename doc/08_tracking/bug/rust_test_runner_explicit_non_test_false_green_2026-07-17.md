# Rust Test Runner Explicit Non-Test False Green

## Status

Fixed in the temporary Rust runner on 2026-07-17.

## Reproduction

```text
SIMPLE_TEST_RUNNER_RUST=1 simple test sibling_describe_green_fixture.spl
Spec files (*_spec.spl): 0
Test files (*_test.spl): 0
Passed: 0
exit: 0
```

The explicitly requested file existed but did not match the runner's discovery
suffixes. Discovery silently returned an empty suite, which the summary treated
as success.

## Fix and Prevention

Any explicit path whose completed spec and doctest discovery is empty now fails
with exit status 1. This also prevents false greens for missing paths and empty
target directories. Full-suite discovery is unchanged. A focused Rust unit test
covers targeted/untargeted, spec, and doctest counts.

The bounded binary-target test command timed out after 180 seconds while still
compiling `simple-compiler`; the test body did not run, and the command was not
retried. Rustfmt and the source contract pass.
