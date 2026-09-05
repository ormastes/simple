# Off-host bug assignment — what a second PC (or a Mac) can fix

Derived 2026-08-17 from the full triage of all 2,630 bug docs
(`doc/08_tracking/bug/`) against **current source**, not the prose in the docs.
Triage result: **1,281 live**, 628 already-fixed-but-stale (29%), 164 closeable,
59 duplicate.

This document answers two questions: *which bugs can be worked away from this
host*, and *how a second machine picks one without colliding with the ~20 lanes
running here*.

## The split

| set | count | where it can be fixed |
|---|---|---|
| **Bootstrap-critical** | ~180 CORE P1 | **this host only** — needs the live stage-2/3 build |
| **Portable** | **582** (P1 150 · P2 432) | any Linux PC |
| ↳ of which **pure-Simple, no build needed** | **449** | any Linux PC, fastest path |
| **Mac-gated** | **42** (P1 8 · P2 25 · P3 9) | macOS host only |

Worklists (TSV, one row per bug):

- `scratchpad/triage/portable.tsv` — 582 portable
- `scratchpad/triage/portable_nobuild.tsv` — 449 pure-Simple subset
- `scratchpad/triage/mac.tsv` — 42 macOS
- `scratchpad/triage/all_db.tsv` — all 1,281 live

Columns: `docfile · verdict · severity · title · file · line · reproducible_by ·
evidence`.

## Why "portable" is defined the way it is

A row is portable when it is live, P1 or P2, and **none** of the following hold:

- it mentions Stage 2/3/4, bootstrap, or self-host — those need this host's build
- it needs hardware this host happens to have (NVIDIA GPU, CUDA, Vulkan ICD,
  QEMU/board lanes, RISC-V, arm64, Intel GPU tooling)
- it lives under `src/compiler_rust/**` — the Rust seed, which needs a ~2h cold
  cargo build and is currently contended here

The **449 pure-Simple subset** is the highest-value slice for a second machine,
for one measured reason: **a `src/lib/**` or `src/compiler/**` `.spl` change
needs no build at all.** The stdlib is read as SOURCE on every process start
(82 `.spl` opens, 0 `.smf`, measured by strace). Edit, run, done. No cargo, no
bootstrap, no toolchain setup beyond a working `bin/simple`.

## How a second PC picks work without colliding

Claim by **hash partition**, not by a shared lock — no coordination service, and
it cannot deadlock if a machine goes away.

```sh
# On machine N of M (0-indexed), take only your shard:
awk -F'\t' -v n=0 -v m=2 '
  { h=0; for (i=1; i<=length($1); i++) h = (h*31 + index("abcdefghijklmnopqrstuvwxyz0123456789_-.", substr($1,i,1))) % 100003 }
  h % m == n
' scratchpad/triage/portable_nobuild.tsv
```

`$1` is the bug doc filename, which is stable, so the same row always lands on
the same machine. Two machines with different `n` can never pick the same bug.

Then push to a **branch per machine**, never straight to `main`. This host has
~20 lanes committing concurrently and has already suffered a silent revert (see
"Hazards" below).

## Non-negotiable rules for any machine doing this work

These are project rules, and each was learned the expensive way today.

1. **Reproduce first.** Quote the RED `Results: N total, N passed, N failed`
   line *before* fixing. **29% of the corpus was already fixed and merely
   mislabelled**, so "did not reproduce — here is the commit/symbol that fixed
   it" is a *good* result. Record the evidence and close it.
2. **Two specs per fix**: a reproducing spec (fails before, passes after) **and**
   a similar-problem detection spec that generalizes to the defect *class*. The
   detection spec caught a gap its own reproducer missed **six separate times**
   today — including one case where the reproducer passed with the fix *removed*.
3. **Classify by CONTENT, never by SHA ancestry.** Constant rebasing rewrites
   SHAs here; commits can be unreachable from `origin/main` while their content
   is present. Grep the fix in current source instead.
4. **A spec body runs INTERPRETED.** A JIT or native defect can never go red from
   a spec body alone — shell out to a subprocess and compare engines. Copy
   `test/01_unit/compiler/codegen/scalar_slot_roundtrip_class_spec.spl`.
5. **Never read an exit code through a pipe** — `cmd | tail` yields *tail's*
   status. Assign `rc` on the next line. This produced two false greens today.
6. **Embedded fixture sources in specs must avoid `{...}` entirely** — the
   *spec's* lexer resolves the interpolation, not the fixture's, and the file
   dies with `zero-examples` before any example runs. Two vacuous specs today.
7. Use `--timeout <n>`, not `SIMPLE_TIMEOUT_SECONDS` (still misbehaves).

## Hazards a remote machine avoids by construction

Worth stating, because they are exactly why off-host work is attractive right
now:

- **This host is saturated.** Load has run 140–187 on 32 cores with 150+
  concurrent `simple` processes. Multiple lanes could not obtain a `Results:`
  line at all; three had specs SIGKILLed (exit 144) rather than merely slowed.
- **Uncommitted edits are not safe here.** A parallel session reverted three of
  one lane's source files to HEAD mid-session, and HEAD moved five times
  underneath it. Another lane's `commit-tree -p HEAD` silently reverted two other
  lanes' fixes.
- **Evidence was corrupted until 06:35.** Three `kill_simple_monitor.shs`
  instances were racing from different worktrees, one running the pre-fix
  `MIN_AGE_SECS=60` — below a normal spec's ~115s runtime. A SIGTERMed spec dies
  before printing its header and launders through a pipe as exit 0 with no
  `Results:` line, i.e. indistinguishable from the silent-green defect class.

A second machine has none of these problems.

## Plan for the Mac work (42 bugs)

The Mac set is genuinely blocked here — no macOS host exists in this fleet, and
it is one of only two categories where a "needs hardware" claim survived probing
(the other is Intel-GPU tooling). Four other "needs hardware" claims were
**disproven** by probing, so do not add to this list without a probe.

Suggested order:

1. **First, re-triage on the Mac itself (cheap, hours).** These 42 rows were
   classified by reading source on Linux. Given the 29% stale rate across the
   corpus, expect a similar share here to be already fixed. Do this before any
   fix work — it is the highest-yield hour available.
2. **Then the 8 P1s.** Concentrated in `src/os` (9 rows overall) and `src/lib`
   (8) — these are the ones that produce wrong results rather than cosmetic
   defects.
3. **`src/compiler_rust` rows (6) need a cargo build**, so budget a cold build
   on first run; the rest are `.spl` and need none.
4. **`examples/09_embedded` (5)** are lowest priority — sample code, not product.

Deliverable from the Mac, per bug: the same reproduce-first evidence and the same
two specs. A Mac-only fix that no Linux machine can verify **must** ship its
reproducing spec, or it is unverifiable for everyone else forever.

## What stays here

Bootstrap-critical work (~180 CORE P1, including the enum-payload owner-conflict
blocker and the aggregate-return field-index defect) stays on this host, because
verifying it requires running the stage-2/stage-3 build that only exists here.
