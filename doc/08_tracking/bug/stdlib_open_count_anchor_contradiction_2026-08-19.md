# Stdlib open-count anchor contradiction — 82 opens vs 0 opens (2026-08-19)

Status: recorded, not yet re-measured. Documentation-only finding; no code or
rules-file change made.

## The two claims

**Side A — `.claude/rules/commands.md:28-34`** (section "A `src/lib/**` change
needs NO build (measured 2026-08-09)"):

> Editing the stdlib requires **no build step at all** for `run` / `test` / lint /
> LSP. The stdlib is read as SOURCE on every process start — measured by strace:
> **82 opens of `src/lib/**.spl`, zero `.smf`**.

(lines 30-32; the "(measured 2026-08-09)" date is at line 28.)

**Side B — `doc/10_metrics/startup/startup_perf_check_2026-08-17.md`**:

- Line 29 (syscall table, `strace -f -c`): `| openat | 14 | 14 |` — 14 openat
  total for both `--version` and `run hello.spl`.
- Lines 50-53 (observation 3):

> 3. **`src/lib` opens: 0** for the hello run. The documented "82 src/lib opens
>    per run" baseline did not reproduce for an import-free script — stdlib
>    loading is evidently lazy on this seed build. No .spl-side I/O above
>    baseline exists to remove.

## Same scenario? **No.**

The two figures describe DIFFERENT scenarios, and the metrics doc says so
itself:

- **Workload differs.** Side B traced `bin/simple run hello.spl` where hello.spl
  is `print("hello")` — explicitly an **import-free script** (doc, line 21 and
  line 50). Side A's claim covers `run` / `test` / lint / LSP generally and its
  example is `bin/simple test test/01_unit/.../foo_spec.spl` — a spec run, which
  pulls in the spec framework from `src/lib` (`nogc_sync_mut/spec`). The exact
  command behind the 82-opens strace is **not recorded** in commands.md — cannot
  determine from the document which invocation produced it.
- **Binary may differ.** Side B pins its binary exactly: Rust seed,
  `bin/release/x86_64-unknown-linux-gnu/simple`, 59,537,240 bytes, mtime
  2026-08-17 12:58:51 UTC. Side A records only "(measured 2026-08-09)" with no
  binary identity — despite commands.md's own rule ("ALWAYS record binary
  identity with any timing"). Eight days and multiple seed redeploys separate
  the two measurements.
- Side B's own interpretation is not "Side A is wrong" but "stdlib loading is
  evidently **lazy** on this seed build" — i.e. opens scale with what the
  program imports, so 0 for an import-free script and some larger N for an
  import-heavy one are mutually consistent.

## Staleness marker check

commands.md's lint-cost table carries an explicit dated warning ("Dated note
(2026-08-18): the table above predates the 2026-08-18 06:12 seed redeploy … and
MUST be re-measured before use"). The 82-opens figure carries **no such
marker** — only the section-heading date "(measured 2026-08-09)". It has not
been flagged stale despite being older than the lint table and already
non-reproducing on 2026-08-17.

## What is therefore actually known

- On the 2026-08-17 seed, an import-free `run` opens **zero** `src/lib` files.
  So the rules-file wording "read as SOURCE on every process start" is
  falsified *as stated universally*: it is at most per-import, not per-start.
- The load-bearing conclusion the 82-opens figure supports — "a `src/lib/**`
  edit needs NO build, because whatever stdlib is used is read from source, not
  from a baked/.smf artifact" — is **not** contradicted by Side B. Side B saw
  zero `.smf` opens too, and lazy source loading still means an edited stdlib
  file is picked up without a build *when it is imported*. The independent
  evidence (no `include_str!` of src/lib) is untouched.
- The literal number 82 has no recorded scenario or binary identity and should
  not be cited as a current fact.

## The one measurement that would settle it

On the current `bin/simple` (recording `readlink -f bin/simple` + size/mtime
first), strace the exact workload Side A's section is about — a stdlib-importing
run, e.g.:

```bash
strace -f -e trace=openat -o /tmp/t.log \
  bin/simple test test/01_unit/lib/<some>_spec.spl   # or: run a script with `use std.X`
grep -c 'src/lib/.*\.spl' /tmp/t.log ; grep -c '\.smf' /tmp/t.log
```

If src/lib `.spl` opens are >0 and `.smf` opens are 0, both documents are
reconciled (lazy per-import source loading) and commands.md only needs its
wording tightened from "every process start" to "whenever std is imported",
plus a binary-identity/staleness note. If src/lib opens are 0 even for an
import-heavy run, the no-build-needed rule itself needs re-verification.

Not run here: this box is memory-critical and the task was static reading only.
