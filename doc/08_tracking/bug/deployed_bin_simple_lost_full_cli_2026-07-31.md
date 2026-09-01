# `bin/simple` deployed as a bootstrap-only binary — `test`/`run`/`lint` all gone (2026-07-31)

**Status:** OPEN, ACTIVE BREAKAGE of the repo's default tooling.
**Detected:** 2026-07-31 ~12:20 UTC, mid-session, between two spec runs.

## Symptom

    $ bin/simple test <any spec>
    error: unknown command 'test'

    $ bin/simple
    Simple Bootstrap Compiler v1.0.0-beta
    Usage: simple compile <file> [-o <output>] [--native] [--opt-level=<level>]

`compile` is the **only** subcommand the deployed binary exposes. `test`, `run`,
`lint`, `fmt`, `build`, `stats` are all absent. Per `.claude/rules/commands.md`
and CLAUDE.md, `bin/simple` is the documented entry point for every one of them,
so the whole documented workflow is dead until this is redeployed.

## What was deployed

    bin/simple -> release/x86_64-unknown-linux-gnu/simple
    130,366,776 bytes, mtime 2026-07-31 12:14

It reports `simple-bootstrap 1.0.0-beta` / "Built from Simple source via the
staged bootstrap" — i.e. it is a build of `src/app/cli/bootstrap_main.spl`, the
reduced bootstrap entry point, **not** the full CLI. It was published straight
over the release path.

Every staged artifact currently on disk has the same reduced surface:

| binary | size | `test`? |
|---|---|---|
| `bin/release/x86_64-unknown-linux-gnu/simple` (deployed) | 130,366,776 | no |
| `build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple` | 127,555,736 | no |
| `build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple` | 127,555,736 | no |
| `build/bootstrap-segv-fix/stage3-fixed/simple` | 127,498,696 | no |
| `simple.bootstrap-clobber-bak` (Jul 23) | 124,596,016 | no |
| `simple.deployed-noLLVM-2026-07-29.bak` | 57,345,808 | seed only, refuses |

So there is **no rollback target in this repo** — the same trap as
`reference_deployed_binary_lost_llvm_codegen_2026-07-29`, where the available
backup was also not a valid rollback.

## Why this is easy to misread

The failure surfaces as `NO_RESULTS` with a 1-line log, which looks like a
compile hang or a runner timeout. It is neither. **Always read the log body when
a spec produces no `Results:` line** — this one says `error: unknown command
'test'` on line 1. A harness that only greps for `Results:` reports this
identically to a real failure.

This adds a fourth entry to the "looks like a failure but isn't" taxonomy
alongside the daemon timeout, the deterministic compiler hang, and the web paint
wall-clock budget flake.

## Impact observed

Five spec re-runs returned `NO_RESULTS` and were initially indistinguishable
from a regression in the code under test. Any spec result recorded after
2026-07-31 12:14 in this working copy is void and must be re-run.

## Fix

Rebuild and deploy the full CLI (`bin/simple build bootstrap`, then re-deploy to
`bin/release/<triple>/simple`). Note a `--full-bootstrap` run is in flight in a
**different** worktree (`simple_release_beta2_wt`), so coordinate rather than
racing it.

Guard worth adding: a post-deploy smoke check that the published binary answers
`test --help`, `run --help` and `lint --help` before it is allowed to replace
`bin/release/<triple>/simple`. A deploy that silently narrows the CLI surface
should fail loudly at deploy time, not at the next contributor's first command.
