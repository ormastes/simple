# Deployed self-hosted `simple test` SIGSEGVs, and bootstrap Stage 1 rejects the same binary

- **ID:** BUG-2026-08-16-selfhost-test-segv-blocks-bootstrap
- **Date:** 2026-08-16
- **Status:** open
- **Severity:** high — no pure-Simple self-hosted test evidence is obtainable
  in-tree, and the documented recovery path (re-bootstrap) is itself blocked
- **Component:** `release/x86_64-unknown-linux-gnu/simple` (git-tracked),
  `scripts/bootstrap/bootstrap-from-scratch.sh`

## Summary

At `origin/main` `f6cadcc36aff61d16d988651ea36a040d2af6aad`, the git-tracked
self-hosted CLI segfaults in its `test` subcommand, and the bootstrap that
would rebuild it refuses to run because Stage 1 probes that same binary.

This is distinct from the existing deployment-state bugs. Those record that
`bin/simple` is *the seed*
(`deployed_bin_simple_still_seed_2026-08-05.md`) or *bootstrap-only*
(`deployed_bin_simple_bootstrap_only_2026-07-31.md`). Neither records that the
self-hosted binary which *is* present is itself crash-broken, nor that this
closes the bootstrap recovery loop.

## Reproduction

Binary identity (tracked in git at the tip above):

```
md5  dcc9f8eae05d512f88d2f5f9fef6af0f  release/x86_64-unknown-linux-gnu/simple
```

It is genuinely the self-hosted build, not the seed — it prints no seed
warning:

```
$ ./release/x86_64-unknown-linux-gnu/simple --version
Simple v1.0.0-beta                      # seed prints a WARNING banner instead
$ ./release/x86_64-unknown-linux-gnu/simple --help    # exit 0, prints usage
```

But every path into `test` dies before producing one byte of output:

```
$ ./release/x86_64-unknown-linux-gnu/simple test --help
Segmentation fault                      # exit 139, zero stdout, zero stderr
$ ./release/x86_64-unknown-linux-gnu/simple test test/01_unit/browser_engine/layout_text_node_spec.spl
Segmentation fault                      # exit 139
```

`test --help` crashing is the sharp end: it takes no spec, loads no stdlib,
and parses nothing. The fault is in the `test` subcommand's own entry path,
upstream of any test content, so no choice of spec avoids it.

## Why the documented recovery is also blocked

`.claude/rules/bootstrap.md` says to re-deploy rather than fall back to the
seed. That path does not close:

```
$ bin/release/x86_64-unknown-linux-gnu/simple build bootstrap \
    --bootstrap-reason=<reason> --bootstrap-receipt=<path>
=== Stage 1: Compile with seed compiler ===
error: deployed Simple runtime failed its bounded test ABI probe:
       <repo>/release/x86_64-unknown-linux-gnu/simple
  Compile failed (exit Some(1))
Stage 1 FAILED
```

Stage 1 gates on a bounded test-ABI probe of the *deployed* runtime — the very
binary whose `test` path is broken — so the probe fails and no receipt is
emitted. `scripts/bootstrap/bootstrap-from-scratch.sh` cannot be used to step
around it either: it hard-requires a receipt that only the blocked planner
produces (`bootstrap-policy-error: reason-receipt-required`).

Net: seed → self-hosted is blocked by the self-hosted binary's own defect.

## The third route is closed too

`bootstrap/stage{1,2,3}/simple` (all three byte-identical,
md5 `2244f18ce2e694fb7ca395e9916404c3`, so the staged fixed point *is* reached)
offer only `compile` and `native-build` — no `test`, no `run`. Compiling a spec
to a native executable and running that would still be pure-Simple self-hosted
evidence, but it fails in the compiler's own frontend:

```
$ bootstrap/stage3/simple native-build \
    test/01_unit/browser_engine/layout_text_node_spec.spl -o /tmp/spec_bin
error: in-process native-build: HIR lowering error in
       test/01_unit/browser_engine/layout_text_node_spec.spl:
       unresolved name: __p-1
[ERROR] phase 3 FAILED                  # exit 1, no binary produced
```

`__p-1` is a generated placeholder name (negative index), so this looks like a
desugar/lowering bug in the bootstrap compiler rather than anything wrong with
the spec.

So all three routes to self-hosted evidence are simultaneously closed:
deployed CLI `test` SIGSEGVs, re-bootstrap is gated on that same binary, and
the staged compiler cannot lower a spec.

## Not the same as stage3-segfault-fix

`.spipe/stage3-segfault-fix/state.md` (AC-3, AC-4 open) covers a Stage 3
`native-build` exit-139 during bootstrap. This bug is in the *already deployed*
binary's `test` subcommand at runtime, and it fires at **Stage 1**, before
Stage 3 is reached. Fixing either one alone does not obviously clear the other,
but this one is what currently prevents the bootstrap from starting.

## Consequence

Any lane whose contract is "pure-Simple self-hosted evidence only, never Rust
seed test evidence" cannot verify anything behaviourally right now. Only static
evidence (grep/AST-level) is available. Encountered while verifying the web
DOM/layout recovery landed in `81684d8af46`; that commit's static verification
passed, but its two specs could not be executed.

## Suggested fix

Debug the `test` subcommand entry path in the self-hosted CLI (it faults before
any output, so a null/uninitialised receiver in subcommand dispatch or runner
init is the first place to look — compare
`deployed_seed_test_runner_init_hang_2026-07-17.md`, which is the same region).
Separately, consider whether Stage 1's bounded test ABI probe should be able to
run against the *seed* when the deployed runtime is known-bad, so that a broken
deployment can always be bootstrapped out of rather than being self-sealing.
