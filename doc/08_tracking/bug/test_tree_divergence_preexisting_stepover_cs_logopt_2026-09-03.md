# Pre-existing test-tree divergence stepped over by the cs / log-opt landing

> Recorded 2026-09-03 to satisfy the scoped-delta escape in
> `.claude/rules/vcs.md` — landing on a delta-PASS REQUIRES recording the
> pre-existing offender list. An unrecorded step-over is a violation even when
> the delta is clean.

## Verdicts

Range: `origin/main..<cs + code-burn + toolchain log-opt plugins>`
(`bin/cs`, `simple_token_burn`, `simple_log_optimize`, `config/log_opt/*.sdn`).

The figures below were measured against base `a5fc77d2c4e` (the `origin/main`
tip at the time of the run). `main` advances every few minutes on this repo, so
the absolute counts drift; the load-bearing number is the DELTA, which is
`0 introduced` and — per the structural argument below — is 0 against ANY base.

```
base verdict: check-test-tree-divergence: FAIL — 3955 diverged vs 965 baselined
  (3085 new, 95 fixed-but-still-baselined); 26 mirror-only (25 unallowlisted,
  0 stale-allowlist); half-landed: skipped (no --base)
delta verdict: PASS — 3205 pre-existing offender(s), 0 introduced by this range
             — "pre-existing red is identical at BASE and NEW; this range
                introduces nothing"
```

Offender list as saved by the helper: 3,955 lines,
sha256 `3e2247fad468a0c89edff5faa84caa81c964df27ca00ae2e3301c855d9a7709a`.
The helper writes it to `$TMPDIR/test_tree_divergence_preexisting.txt`, which
is not durable; the counts and digest above are the durable record, and the
list is reproducible at any time with
`sh scripts/check/check-test-tree-divergence.shs --ref origin/main`.

## Why this range structurally cannot contribute

The only test file the range adds is
`test/01_unit/app/mcp/log_opt_burn_spec.spl`, which is **canonical-only** — it
has no `test/unit/app/mcp/log_opt_burn_spec.spl` twin on either side of the
range (`git cat-file -e origin/main:test/unit/app/mcp/log_opt_burn_spec.spl`
→ "does not exist"). Per `scripts/check/check-test-tree-divergence.shs:242-260`
the scan iterates the **shadow** tree and classifies a shadow path with no
canonical counterpart as mirror-only, while canonical-only paths are the norm
(the shadow trees are deliberate partial subsets) and are never enumerated at
all. A canonical-only addition is therefore neither a common pair nor
mirror-only: it cannot enter any offender category.

This was predicted from the guard's source before the delta run finished, and
the mechanical verdict then confirmed it — `0 introduced` — so the structural
argument and the measurement agree.

## Trend worth noting, not owned by this lane

The comparable record `test_tree_divergence_preexisting_stepover_2026-08-17.md`
logged `875 diverged vs 812 baselined (64 new)`. Seventeen days later the base
reads `3955 diverged vs 965 baselined (3085 new)` — the new-divergence figure
has grown ~48x while the baseline moved by 153. Each individual step-over is
legitimate under the scoped-delta rule and each is recorded, but the aggregate
says the baseline is no longer tracking the tree, and the ratchet has stopped
ratcheting in practice. Whoever owns the test-tree dedup lane should decide
between a reviewed `--generate-baseline` refresh and a real reconciliation;
neither is in scope for this lane, and this record exists so the growth is not
invisible.

## Status

OPEN (the pre-existing red is not this lane's to fix). The step-over itself is
closed by this record.
