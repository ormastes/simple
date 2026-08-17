# Deployed `bin/simple` is a bootstrap-only binary: no `test`/`run`/`lint`, and cannot parse `@extern`

- **Date:** 2026-07-31
- **Severity:** blocker (no test runner on this machine)
- **Component:** deploy / bootstrap binary
- Status: CLOSED — did not reproduce (2026-08-17, wave_01 lane H3; see the
  re-verification section at the end of this file for the probe transcripts)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).

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

---

## 2026-08-17 re-verification (wave_01 lane H3) — DID NOT REPRODUCE, both claims dead

Classified by direct probe of the CURRENTLY deployed artifact, not by SHA
ancestry. Binary identity recorded first, per `.claude/rules/commands.md`:

```
$ readlink -f bin/simple
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
$ stat -c '%s %y' "$(readlink -f bin/simple)"
59536728 2026-08-16 22:59:37.799277177 +0000
```

**Claim 1 — "full CLI is missing" — FALSE against this artifact.** The report's
signature failure was `error: unknown command 'test'`. That string does not
occur:

```
$ nice -n 19 timeout 60 bin/simple test --help ; echo rc=$?
rc=124
WARNING: this Rust-built Simple binary is a bootstrap seed only; ...
warning: Avoid 'export use *' - exposes unnecessary interfaces
  --> src/lib/nogc_async_mut/test_runner/test_runner_types.spl:1:1
```

`test` is RECOGNISED — the binary proceeds into module loading (the ~310s
session-setup path) and my 60s cap expired; rc=124 is my `timeout`, not a
rejected subcommand. `lint --help` behaves identically. The binary is a full
CLI seed, not the bootstrap-only build described here.

**Claim 2 — "`compile` cannot parse a bodiless `@extern fn`" — FALSE.**

```
$ cat /tmp/h3/extern_probe.spl
@extern fn rt_probe_noop() -> i64

fn main():
    println("ok")
$ nice -n 19 timeout 300 bin/simple compile --format=smf /tmp/h3/extern_probe.spl ; echo rc=$?
rc=0
Compiled /tmp/h3/extern_probe.spl -> /tmp/h3/extern_probe.smf
```

**Verdict: CLOSED — not reproducible.** The bootstrap-only artifact this report
describes was replaced; the deployed binary is now a full-CLI Rust seed. The
*separate* fact that it is still a SEED rather than the self-hosted binary is a
different defect and stays open under
`deployed_bin_simple_still_seed_2026-08-05.md` — do not merge the two. No source
fix was made and none is warranted: this report tracked a deployment state, not
a source defect.
