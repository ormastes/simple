# Spec-Vacuity Families 3 & 4 — Full-Corpus Census

_Driver: `scripts/check/census-spec-vacuity.spl` (landed `bbe4682d52b`)._
_Status: **IN PROGRESS** — corpus/dedup section final, scan results pending._

## What this census is, and what it is not

Four spec-vacuity families are known in this repo:

1. **Non-matcher `expect` tail** — a tail method that exists on the argument's
   type but is not a matcher, so nothing is asserted. **GATED** at `47ba20fda2b`;
   its full-corpus RED census is a *separate* document,
   `expect_vacuity_gate_full_corpus_census.md` (execution-based, 2372/9872 at
   `b5b1b11b2fb`).
2. **The needle matches only a COMMENT** in the product source. Not yet gated;
   no automated scorer.
3. **A value-type helper mutates a COPY** — codes `VTM001` / `VTM002`.
4. **The spec re-implements the code under test, in-spec** — codes `SHADOW` /
   `NOSRC`.

**This document covers families 3 and 4 only.** They are the two families the
census driver scores, and unlike family 1 the driver is *static*: it does not
execute specs, so it is not subject to the daemon/timeout/no-verdict infra noise
that dominates the family-1 census buckets.

Positive control is fatal and reproduced on every run:

```
control: 5 planted VTM violations detected, 8 correct forms silent
control: SHADOW fires on a colliding name, silent on a spec-only name
```

## Corpus and duplicate-tree dedup

`test/01_unit` ≡ `test/unit` and `test/03_system` ≡ `test/system` are duplicate
trees and **both execute**. Counting them naively double-counts nearly half the
corpus.

| measure | count |
|---|---|
| raw `*_spec.spl` under `test/` | 19,599 |
| unique by content sha256 | 9,940 |
| **duplicate files (raw − unique)** | **9,659 (49.3% of raw)** |

Per-mirror-pair breakdown (files present at the same relative path in both
trees):

| pair | paired files | byte-identical | divergent |
|---|---|---|---|
| `test/01_unit` ↔ `test/unit` | 5,006 | 4,178 | 828 |
| `test/03_system` ↔ `test/system` | 336 | 276 | 60 |

Two things follow, and both matter for any gate built on these numbers:

- The mirrors are **not** clean copies. 888 paired files diverge in content, so
  a fix landed in one tree is not automatically live in the other, and a
  finding in one tree must be checked in its twin by hand rather than assumed
  identical.
- `test/01_unit` (7,497 specs) is much larger than `test/unit` (5,013) and
  `test/03_system` (3,363) than `test/system` (1,862) — the numbered trees are
  supersets, not renames. Divergence is fenced by
  `scripts/check/check-test-tree-divergence.shs` against
  `scripts/check/test_tree_divergence_baseline.txt`.

The driver's own `dup` flag classifies a path as duplicate-tree by prefix, and
every finding count below is reported **deduped / raw**.

## Method notes (reproducibility)

- Binary: `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`. It
  announces itself as the Rust bootstrap seed. `bin/simple` was **not** touched
  or relinked.
- The driver's module drops to the **interpreter** (`[jit-fallback] unresolved
  external symbol 'rt_file_is_char_device'`), costing the documented ~100-1000x.
  A whole-corpus run is therefore tens of minutes, not seconds.
- `SIMPLE_TIMEOUT_SECONDS=0` is **required**. Without it
  `kill_simple_monitor` SIGTERMs the run at 60s CPU and the census dies with no
  verdict line — indistinguishable from a clean zero unless you read the
  `TIMEOUT: killed by kill_simple_monitor` line.
- Chunking by root is counter-productive: `build_kind_index` re-scans all of
  `src/` on **every** invocation, so N chunks pay the dominant fixed cost N
  times. One whole-`test/` run is the cheapest form.

## Results

_Pending — the full-corpus run is executing. This section is filled in on
completion and pushed immediately._
