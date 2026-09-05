# `test/unit/` is a rotting legacy mirror of `test/01_unit/` — and BOTH run

Date: 2026-08-04
Base measured: origin `main` @ `44bf140626b313d9b51f647c493ad0336133d45d`

## Summary

`test/unit/` and `test/01_unit/` are separate regular files (not symlinks). Both
trees are discovered and executed by `bin/simple test`. **874 paths present in
both trees have different content**, so those specs produce two different
verdicts for the "same" spec. `test/unit/` is uniformly the older, thinner tree:
its greens are frequently vacuous and its reds are frequently false.

## 1. Four-way census (origin tip, blobs only)

`git ls-tree -r` was used, not a filesystem walk. `ls-tree -r` does **not**
recurse through symlinks (they are mode-120000 blobs), so the 23 directory
symlinks under `test/` — 8 of them under these two trees, including
`test/unit/compiler/compiler -> ../../../src/compiler` and
`test/unit/compiler/std -> ../../../src/lib` — contributed no `src/` aliases.

| Class | Count |
|---|---|
| Present in both, **byte-identical** | 7,412 |
| Present in both, **differing** | **874** |
| Present only in `test/01_unit` | 2,165 |
| Present only in `test/unit` | 22 |
| Union of paths | 10,473 |

Tree totals (blobs, excluding symlinks): `test/01_unit` 10,451, `test/unit` 8,308.

Of the 22 `test/unit`-only entries, only **3 are real spec files**; the other 19
are 17 `compiler/verification/*/summary.txt` artifacts and 2
`*.jit.note.sdn` notes.

## 2. Why they diverged — a frozen mirror, not a forgotten twin

The two trees were **never identical**. Divergence at the birth commit
`97a9358145f` (2026-07-01) was already 694 pairs and has grown monotonically:

| Revision | date | `01_unit` | `unit` | common | identical | **differ** |
|---|---|---|---|---|---|---|
| `97a9358145f` | 07-01 | 8,917 | 8,317 | 8,283 | 7,589 | 694 |
| `fc52ff839ce` | 07-11 | 9,206 | 8,320 | 8,285 | 7,536 | 749 |
| `26a5e739407` | 07-20 | 9,527 | 8,310 | 8,275 | 7,457 | 818 |
| `a8f456d8442` | 07-28 | 9,843 | 8,312 | 8,276 | 7,404 | 872 |
| tip `44bf1406` | 08-04 | 10,451 | 8,308 | 8,286 | 7,412 | **874** |

`test/01_unit` grew by 1,534 files in a month; `test/unit` is **flat** (8,317 →
8,308). Commits touching `test/01_unit`: **2,710**. Touching `test/unit`: **199**.
The identical-count *falls* over time. This is a frozen mirror rotting, not a
pair of lanes forgetting each other.

The observed diffs are the wake of source-tree refactors that landed only in the
maintained tree, e.g.:

- `src/compiler/90.tools/migrate/main.spl` (01_unit) vs `src/app/migrate/main.spl` (unit)
- `use app.doc_coverage.tagging.tag_validator...` vs unprefixed `use doc_coverage...`
- de-duplicating renames (`dlr_list_has` vs `dlr_dlr_list_has`)

### Timestamp recency is NOT usable here — a measurement trap

Both tree wipes (`beea94b72ce`, `118c636ead8`) were repaired by restore commits
(`b6234c8b6a0`, `7f5a55fa46e`) that **rewrote every blob in the repo**. So the
last-touch commit for 837/874 differing pairs is a restore commit, identical on
both sides. Any `git log`-recency ranking of these pairs is an artifact of the
restores, not evidence of authorship order. The restores themselves were
faithful: divergence was 882 both immediately before and immediately after the
wipe. Direction had to be established by **content and example counts** instead.

## 3. Which tree runs: BOTH (proven)

Discovery has no allowlist — it is a plain recursive walk of `test/`:

- `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:575` — default `path = "test/"`
- `src/lib/nogc_sync_mut/test_runner/test_runner_files.spl:339-344` — `dir_walk(base_path)`, unrestricted
- `src/lib/nogc_sync_mut/test_level_detect.spl:7-8` — explicitly documents both a
  "numbered (maintained)" and a "bare (legacy mirror)" tree; `matches_level`
  (`test_runner_files.spl:95-98`) matches both. No skip list mentions `test/unit`.

Empirical proof #1 — the live discovery index `.simple/test-manifest.idx`
(mtime Aug 4 05:01) contains **6,975** `test/01_unit/` entries and **5,055**
`test/unit/` entries, including the same spec twice with different sizes:

```
2304:test/01_unit/app/cmm_lsp/cmm_dialog_label_ref_spec.spl|10833|...
14096:test/unit/app/cmm_lsp/cmm_dialog_label_ref_spec.spl|10837|...
```

The 4-byte delta is exactly the `dlr_list_has` → `dlr_dlr_list_has` rename.

Empirical proof #2 — running both copies of that spec (seed `bin/simple run`):

| copy | verdict |
|---|---|
| `test/01_unit/app/cmm_lsp/cmm_dialog_label_ref_spec.spl` | `14 examples, 0 failures` (rc=0) |
| `test/unit/app/cmm_lsp/cmm_dialog_label_ref_spec.spl` | `14 examples, 11 failures` (rc=1) |

Same example count (so this is not a module-load dropout) and opposite verdicts.

## 4. Scale of the damage — 60-pair random sample, both sides run

| outcome | pairs |
|---|---|
| both green | 40 |
| **`01_unit` GREEN / `unit` RED** (false red from the mirror) | **8** |
| both red | 5 |
| `01_unit` RED / `unit` GREEN | 1 |
| no verdict one side | 3 |

**20 of 60 pairs (33%) reported different example COUNTS**, several extreme:
33/2, 23/5, 18/10, 13/1, 12/3 — i.e. the mirror copy is a much thinner
pre-expansion version reporting green.

Extrapolated to all 874 differing pairs: roughly **120 pairs where the stale
mirror is red while the maintained spec is green**, plus ~290 pairs where the
mirror silently reports a green over far fewer assertions.

The single "reversed" case is illusory: `app/formatter_spec.spl` is
`5 examples, 2 failures` in `01_unit` but `1 example, 0 failures` in `unit` —
green only because it is a one-example stub. **No differing pair in the sample
showed `test/unit` genuinely ahead.**

## 5. What was resolved here

The only content `test/unit` holds that `test/01_unit` does not is 3 real specs.
These were copied into the maintained tree (verified to pass from the new
location, with identical example counts, and sabotage-verified):

| spec | examples | sabotage | result |
|---|---|---|---|
| `compiler/backend/llvm_bootstrap_accumulator_reset_spec.spl` | 3 | `llvm_bootstrap_string_globals_text()` forced to `""` | 3 ex, **1 failure** → restored 3/0 |
| `compiler_core/interpreter/match_fallthrough_diagnostic_spec.spl` | 9 | `match_fallthrough_message` early-returns `"no arm matched"` | 9 ex, **8 failures** → restored 9/0 |
| `compiler/driver/genuine_import_ownership_spec.spl` | 3 | `db_atomic.spl` import merged to `{parse, SdnValue}` | 3 ex, **1 failure** → restored 3/0 |

Every arm bit, and example counts stayed constant under sabotage (no dropout).

The 874 differing pairs were **not** mechanically synced — see the
recommendation below; syncing them would be ~874 files of work into a tree that
should probably not exist.

## 6. Structural recommendation (decision required — NOT implemented)

**Recommendation: stop discovering `test/unit/`, then delete it.**

Evidence:

1. It is not a mirror anyone maintains — 199 commits vs 2,710, file count flat
   for a month while the twin grew by 1,534.
2. It was never in sync — divergence was already 694 pairs at birth and only
   ever grows.
3. It costs a full duplicate run of 5,055 indexed spec files per `bin/simple test`.
4. It injects ~120 false reds and ~290 vacuous greens into the aggregate verdict.
5. After the 3 migrations above, it holds **no unique spec content**.

The remaining `test/unit`-only artifacts (17 `compiler/verification/*/summary.txt`,
2 `.jit.note.sdn`) should be checked for consumers before deletion.

Note also that `test/FILE.md:5-24` already omits `unit/` from its allowed
entries, and `test/README.md:5-15` documents the bare layout while its own
examples use the numbered one — the docs are already inconsistent about which
tree is real.

A smaller interim step, if deletion is too aggressive: add `test/unit/` to the
discovery skip list in `test_runner_files.spl:360-395` (which already excludes
`/fuzz/`, `/deploy/`, `/security/`, etc.). That stops the false verdicts and
halves unit-tier runtime without deleting anything.
