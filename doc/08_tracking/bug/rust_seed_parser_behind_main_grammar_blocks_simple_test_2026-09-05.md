# The Rust seed's parser is behind main's grammar, so `simple test` cannot run on this host

**Date:** 2026-09-05 (macOS, aarch64)
**Status:** OPEN
**Severity:** blocks the whole test sweep on this host

## Symptom

`simple_seed test <dir>` never reaches a single example. It dies at module
load, and it dies at a *different* stdlib file each time one is worked
around — a chain, not a single defect:

| file | seed's parse error |
|---|---|
| `src/lib/common/perf/execution_metrics.spl:365` | `expected expression, found Indent` |
| `src/lib/nogc_sync_mut/mcdc/dynamic_aspect.spl:257` | `expected expression, found Assign` |
| `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl` | `expected expression, found Dedent` |

## Root cause — the stdlib is NOT broken

Each of those files parses **cleanly** under main's own pure-Simple
compiler:

```
bin/local/phase2-aarch64-apple-darwin/simple compile --format=smf -o /tmp/o.smf \
    src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl
[bootstrap-error-count] source_idx=0 point=post-diagnostics count=0
```

So the grammar main is written in is valid; the **Rust seed's parser is
behind it**. The two forms the seed rejected are both ordinary in this tree:

```simple
if a <= 0.0 or b < 0.0 or          # trailing operator, indented continuation,
        c <= 0 or d < 0:           # NOT wrapped in parentheses

if result: self.arr[slot] = self.arr[slot] | bit   # inline `if` whose body assigns
```

## Why this was nearly mis-filed

Both sites were first "fixed" in source (parenthesise the condition; expand
the inline `if` to a block) and both fixes worked — which is exactly how a
stale-tool problem gets laundered into a permanent source workaround. The
edits were reverted once the phase2 binary proved the grammar valid. Nothing
in `src/lib/**` should be reshaped to please the seed.

## The real blocker

There is still no FULL-CLI pure-Simple binary deployed on this host:
`bin/simple`, `bin/release/aarch64-apple-darwin-macho/simple` and
`bin/local/phase2-aarch64-apple-darwin/simple` are all the BOOTSTRAP CLI
(`compile` / `native-build` only — `src/app/cli/bootstrap_main.spl`), and
`bin/release/aarch64-apple-darwin/simple_seed` is the Rust seed. So the only
binary with a `test` command is the one whose parser cannot read the tree.

Fix is a Stage-4 full-CLI redeploy, not a source change. Until then, the
per-spec lane `simple_seed run <spec>.spl` still works (it loads far fewer
modules) and is the only way to execute a spec on this host.

## Impact on the `@tag:in-development` lane

`src/lib/nogc_sync_mut/spec/in_development.spl` and its runner wiring were
restored the same day and the pure classification layer is verified
(`simple_seed run test/01_unit/lib/spec/in_development_tag_spec.spl` ->
21 examples, 0 failures). The **end-to-end** behaviour — a tagged failing
spec being neutralised in a real sweep — remains UNVERIFIED on this host for
the reason above, and is stated as unverified rather than assumed.
