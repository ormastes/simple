# Pure-Simple test runner executes ZERO specs — trait/impl arity mismatch in `MirToLlvm`

**Status:** OPEN (semantic analysis / trait conformance).
**Found:** 2026-08-04, while measuring `test/03_system/core` with a pinned worktree.
**Impact:** the **default** runner cannot execute any spec at the affected pin.
Fails loudly, but is easily misread as host slowness or a hung run.

## Symptom

Every invocation of the pure-Simple runner — single file and whole directory
alike — dies before executing a single spec, printing no `Results:` line:

```
error: semantic: type MirToLlvm implements method translate_block_at from trait
MirTextCodegen with 7 parameter(s), but the trait declares 5
error: semantic: type MirToLlvm implements method translate_call_at with 3
parameter(s), but the trait declares 2
```

Zero examples run. Because there is no `Results:` line at all, a caller that
greps for a verdict sees nothing and may conclude the run is merely slow. At the
time this was found, a whole measurement lane had already been written off as
"starved by host load 44–56" — the real cause was almost certainly this.

## Repro

```bash
PIN=$(git ls-remote origin main | cut -f1)
git worktree add --detach /tmp/pin_runner $PIN
cd /tmp/pin_runner
ln -sfn /path/to/simple bin/simple
SIMPLE_TIMEOUT_SECONDS=0 ./bin/simple test test/03_system/core/edge_case \
  --no-cache --no-cover-check
```

Observed at pin `851a0e8d82e0`. `SIMPLE_TIMEOUT_SECONDS=0` is required
independently — a monitor daemon kills runs older than 60s.

## Workaround used (NOT a fix)

`SIMPLE_TEST_RUNNER_RUST=1` routes to the Rust interpreter and runs the tier
normally (5,573 examples, both arms). That was acceptable there only because the
change under test was Rust-side. **It is not a general substitute:** stdlib
`.spl` behavior is not exercised by the Rust runner, so any measurement taken
this way says nothing about the pure-Simple path.

## Why this matters

Per `.claude/rules/bootstrap.md` the default tooling is the pure-Simple
self-hosted binary; the Rust seed is bootstrap-only. A repo state where the
default runner executes zero specs means the self-hosted path is untested by
every lane that silently falls back — and a fallback that produces plausible
numbers is exactly how a broken path stays hidden.

## Fix direction

Reconcile the declarations. Either the `MirTextCodegen` trait declares too few
parameters for `translate_block_at` (5 vs the 7 the impl provides) and
`translate_call_at` (2 vs 3), or `MirToLlvm` carries extra ones. Find which side
moved — `git log -S translate_block_at` on both the trait and the impl — and
correct the side that drifted rather than padding the other to match.

Worth checking at the same time why a trait-conformance error is fatal to the
*test runner* rather than scoped to the offending module: the specs being run do
not depend on `MirToLlvm`.

Related: `optional_passed_to_bool_param_is_neither_coerced_nor_rejected_2026-08-04.md`
(the measurement that surfaced this).
