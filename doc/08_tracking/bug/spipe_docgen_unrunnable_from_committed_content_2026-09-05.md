# `spipe-docgen` does not run from committed content, on any spec

## Status

Open. Not a regression in any one spec — the command is unrunnable for every
input when the tree is built from committed content rather than the shared
working copy.

## Severity

Landing blocker for the `spipe_docgen` lane, and a trap for anyone building
from a snapshot. Since `3d9c3873444` the bootstrap runs against an immutable
`git worktree` snapshot of committed content, so this is now on the bootstrap's
path, not only a developer convenience.

## Reproduction

From a checkout of `67859c96792` — `main`'s tip as of 2026-09-05 15:10, since
advanced — on an **untouched** pre-existing spec:

```sh
bin/simple spipe-docgen test/01_unit/app/sspec_maintain/cache_spec.spl \
    --output doc/06_spec --no-index
```

```text
Processing specs:
  OK cache_spec (60 lines)
error[E1002]: function `spec_kw_line` not found
  = help: check the function name or import the module that defines it
```

Exit 1. Reproduced on `sspec_maintain/cache_spec.spl` and on a newly written
spec, so it is input-independent.

## The trap: it fails on a different symbol each time you fix the last one

This is the part worth knowing before you start. Adding the missing 5-line
`spec_kw_line` to `common.spl` resolves that error and produces the next:

```text
error[E1002]: function `scenario_at_is_unconditional_pending` not found
```

(`parser.spl:1802`.) Each round looks like "one small fix away". It is not.
The committed tree is missing a coherent feature spread across four files:

```text
git diff --stat -- src/app/spipe_docgen/ src/app/sspec_maintain/analyzer.spl
    src/app/spipe_docgen/spipe_docgen/common.spl    |  5 +
    src/app/spipe_docgen/spipe_docgen/generator.spl |  8 +-
    src/app/spipe_docgen/spipe_docgen/parser.spl    | 82 ++++++++
    src/app/sspec_maintain/analyzer.spl             | 13 +-
    4 files changed, 105 insertions(+), 3 deletions(-)
```

The committed `generator.spl` and `parser.spl` already reference the symbols;
only the definitions are unlanded. Three of the four files are dirty in the
shared working copy, which is why the failure is invisible to anyone working
there.

## Why the obvious workaround is wrong

Porting the missing definitions into a commit means committing another lane's
entire in-progress change under a different lane's name. If that lane later
changes the behaviour rather than just the location, the tree carries two
definitions that silently disagree — worse than the current loud failure. A
partial port was attempted on 2026-09-05 and **reverted** for exactly this
reason.

Hand-writing a `doc/06_spec` manual to fill the gap is also wrong: a mirror that
claims to be generated, but is not, cannot be distinguished from a real one by
the next reader.

## Required resolution

The lane holding the uncommitted change lands it. Nothing else in the tree needs
to move.

## Consequences until then

- No `doc/06_spec` mirror can be produced for any spec from committed content.
  Specs landed meanwhile owe a mirror that is outstanding, not waived.
- A caller that reads only the first line of docgen's output sees
  `OK <spec> (N lines)` and records a success that produced no manual. The
  error follows on a later line and the exit status is 1 — check the status,
  not the first line.

## Verification scope

Reproduced against `67859c96792` only. `main` has since moved (local
`88c59bed70d`; remote `refs/heads/main` = `320e6d99e4b8b8540a65078f68ce8ffca15fd2b6`,
not fetched locally). If the missing half lands in between, this record goes
stale — re-run the reproduction above before acting on it.

Note when checking the remote: `git ls-remote origin main` is ambiguous on this
remote (592 heads; it returns `refs/heads/archive/2026-09-03/main` first). Ask
for `refs/heads/main` explicitly.

## Related

- `doc/05_design/platform/structural_compute/parser_sharing_contract_v1.md`
  (where this was found, and the specs whose mirrors it blocks)
- `doc/08_tracking/bug/bootstrap_reads_transiently_broken_shared_working_copy_2026-09-05.md`
  (snapshot-build contention; this is a committed-content counterexample to the
  "committed content is buildable" premise a snapshot wrapper rests on)
