# todo_db.sdn reconciliation against source — 2026-08-18

Verdict: **hand-repair, do not regenerate** — the regeneration was run and measured (§ 3, § 5).

Measured reconciliation of `doc/08_tracking/todo/todo_db.sdn` against the actual
working tree at `e9e22a1230f` (worktree `/mnt/data/worktrees/todo-reconcile`,
clean checkout of `origin/main`). Every number below is re-derivable from the
commands in § Method.

**Nothing was closed by this pass.** No row status was changed. This document
records citation validity, not defect liveness — see § The distinction.

## 1. Citation validity — 735 rows

Row count in the db is **735**, not 721 (ids run 0..833, sparse). All 735 rows
carry keyword `TODO`; there are no FIXME/HACK/XXX rows.

A row's citation is checked by: does `file` exist, and does `sed -n '<line>p'`
on it contain `TODO|FIXME|HACK|XXX`.

| class | rows | % |
|---|---|---|
| **VALID** — marker present at cited `file:line` | **373** | 50.7% |
| **NO_MARKER** — file exists, cited line has no marker | **276** | 37.6% |
| **FILE_GONE** — cited file does not exist | **76** | 10.3% |
| **DRIFT_NEAR** — no marker at line, but one within ±5 lines | **10** | 1.4% |

Cross-tabulated with the db's own `status` column:

| class | open | blocked | done |
|---|---|---|---|
| VALID | 373 | 0 | 0 |
| NO_MARKER | 180 | 59 | 37 |
| FILE_GONE | 74 | 1 | 1 |
| DRIFT_NEAR | 9 | 1 | 0 |

**Not one `blocked` or `done` row has a valid citation.** Those 99 rows (61 + 38) are
hand-authored task entries whose `file`/`line` is a pointer into code, not a
scanner hit — a regeneration would delete every one of them. That is the single
most important constraint on the repair strategy (§ 5).

Of the 276 NO_MARKER rows, they cite **193 distinct files**. Of those files,
**154 contain no TODO/FIXME anywhere at all** and **39 still contain markers
elsewhere in the file**. The 39 are pure line drift; the 154 mean the marker was
deleted from source (or never existed there).

### Confirmation of the three lanes' spot findings

- **Rows 6, 40, 96, 155, 355, 418, 487** — all seven NO_MARKER, all cite line
  129, all byte-identical text, seven different paths:
  `src/lib/…/io/signature_sffi.spl`, `src/std/…`, `test/01_unit/compiler/std/…`,
  `test/01_unit/lib/database/lib/…`, `test/unit/lib/database/lib/…`,
  `test/unit/compiler/std/…`, `test/feature/lib/lib/…`.
  The source file has **zero** markers (305 lines). `git log --all -S 'wraps
  SFFI [u8] returns as Option'` finds the text only in three tracking docs
  (`todo_db.sdn`, `doc/09_report/todo_p1_live_db_triage_2026-07-27.md`,
  `doc/09_report/todo_p1_p2_triage_2026-07-27.md`) — never in any source file
  in reachable history. Seven rows, one phantom.
- **Rows 605-651** — 45 rows in range, **45 of 45 NO_MARKER**, 0 valid.
  (The earlier lane sampled 15 and found 0 valid; the full range agrees.)
- **Rows 558, 561, 614, 617, 618, 619, 620** — all seven NO_MARKER.
  `src/compiler/70.backend/backend/cuda_backend.spl` (1776 lines, cited by 614 /
  617 / 619) has zero markers. `src/compiler/10.frontend/core/tokens.spl` (cited
  by 561) still has 4 markers — but not at line 519: line drift, not deletion.

FILE_GONE rows are concentrated in the test trees: `test/01_unit` 28,
`test/02_integration` 17, `test/05_perf` 13, `test/03_system` 10, `src/app` 3,
`test/unit` 2, `test/feature` 2, `src/compiler` 1.

## 2. Duplicate clusters — how many distinct TODOs

Rows cluster by mirrored trees. Path-prefix census of the 735 rows:

| prefix | rows | | prefix | rows |
|---|---|---|---|---|
| test/01_unit | 126 | | src/lib | 48 |
| test/unit | 99 | | test/feature | 47 |
| test/02_integration | 59 | | test/integration | 40 |
| src/compiler | 50 | | scripts/check | 38 |
| test/03_system | 48 | | test/05_perf | 33 |
| src/std | 31 | | src/compiler_rust | 21 |

**480 of 735 rows (65%) cite a path under `test/`.** Both mirror pairs are live
(`test/01_unit` + `test/unit`, `test/02_integration` + `test/integration`,
`test/03_system` + `test/system`, `test/05_perf` + `test/perf`, plus
`test/feature`), and `src/lib` + `src/std` are both present, so a scanner that
walks the whole tree records the same TODO up to 7 times.

Two clustering keys, giving a lower and an upper bound on distinct TODOs:

| key | distinct | redundant rows |
|---|---|---|
| (description, line) — merges same TODO in genuinely different files | **374** | 361 (49%) |
| (description, line, basename) — keeps same-named files apart | **430** | 305 (41%) |

54 clusters mix basenames; those are real source duplication (e.g.
`engine/render/gpu_mesh3d.spl` existing under both `nogc_sync_mut` and
`nogc_async_mut`), so **430 is the defensible distinct-TODO count** and 374 the
floor. Either way the db's 735 rows overstate real work by **1.7x-2.0x**.

Largest clusters (14 rows each, all mirrors of one marker):
`upload real f64→[u8] per-instance transform data…` (line 161),
`serialize InstanceData fields into real bytes…` (177),
`replace placeholder zeroed serialization with real f32→[u8] packing` (297),
`replace placeholder zeroed byte buffers with real float serialization` (93),
`real float serialization — build zeroed placeholder bytes for now` (104),
`real f32/i64 serialization — zeroed placeholder for now` (305).
Then 8 rows each for `wire up hwprobe when available` (349) and `original
phantom API filtered excludes…` (70).

Counting only rows whose citation is **VALID**, deduped by
(description, line, basename): **142 distinct live TODOs** out of 373 valid rows.

## 3. Independent ground truth, and `bin/simple todo-scan`

### Ground-truth marker census (does not depend on todo-scan)

Over tracked, non-vendored `*.spl|*.shs|*.rs|*.c|*.h` under
`src/ test/ scripts/ examples/` (41,405 files; vendor excluded per CLAUDE.md
Owned-Code Scope):

- **1,627** lines matching `TODO|FIXME` anywhere, in 511 files (includes prose
  and test-string mentions).
- **713** lines matching the comment form `(//|#|--|/*) (TODO|FIXME)[:( ]` —
  the population a marker scanner should find.
- Deduped by (basename, marker text): **528**. By text alone: **500**.

So the tree holds ~713 marker instances / ~528 distinct TODOs, against a db of
735 rows / ~430 distinct. **The db is not merely inflated — it is inflated *and*
incomplete**: it duplicates what it has while missing markers that exist. It is
not a subset and not a superset of source truth.

### `bin/simple todo-scan` — completed run

Run per `.claude/rules/commands.md` (it rewrites `doc/TODO.md` and
`doc/08_tracking/todo/todo_db.sdn`, so it was run in this isolated worktree with
both files backed up first, detached via `nohup setsid`, never wrapped in
`timeout`). Wall time ~20 min. Terminal output:

```
Scanning TODOs from /mnt/data/worktrees/todo-reconcile
Found 56505 source files to scan
Scan complete: 267 TODOs found
Database saved to .../doc/08_tracking/todo/todo_db.sdn
Generated docs to .../doc/TODO.md
RC=0
```

The generated db was saved to `/mnt/data/tmp/tr/after_scan_db.sdn` and the
working copy was then restored with `git checkout --` (back to 735 rows). The
generated output is **not** committed.

| | current db | todo-scan output | source ground truth |
|---|---|---|---|
| rows / marker instances | 735 | **267** | 713 |
| distinct (desc, line, basename) | 430 | **166** | 528 |
| `open` | 636 | **267** | — |
| `blocked` | 61 | **0** | — |
| `done` | 38 | **0** | — |

Three conclusions, all decisive:

1. **Regeneration destroys all 99 curated rows.** The output has no `blocked` and
   no `done` row and carries no `blocked`-reason prose. Every record of *why*
   work stopped is lost.
2. **Regeneration does not fix duplication.** 267 rows collapse to 166 distinct —
   still **38% redundant** — and the mirror trees are still the top contributors:
   `test/integration` 39, `test/02_integration` 39, `test/03_system` 32,
   `test/unit` 30, `src/lib` 26, `test/01_unit` 25, `test/05_perf` 17,
   `test/system` 15. Both halves of every mirror pair are still walked.
3. **Regeneration also loses real work.** Set-differenced on
   (description, line, basename): **141 keys in both**, **25 only in the new
   scan**, **289 only in the current db**. And the scan's 166 distinct is well
   under the 528 distinct comment-form markers actually present in tracked
   source — the scanner **under-finds by roughly 3x** while still duplicating
   what it does find.

`Found 56505 source files` is also **15,100 more than the 41,405 tracked source
files**: discovery walks untracked and build output as well as the mirrors. Note
the scanner nevertheless finds fewer TODOs than a plain grep over a *smaller*,
correct file set — so the defect is in its matching, not only its discovery.
## 4. The distinction: citation invalid ≠ defect gone

**No row was marked done by this pass, and none should be on this evidence
alone.** A citation check is a check on a `file:line` pointer, nothing more.
Three independent findings today cut in both directions — a live defect can sit
behind a stale citation (row 561's marker moved within `tokens.spl`; the defect
was real), and a dead TODO can sit behind a perfectly parseable one.

Closing a row requires execution evidence quoting the exact
`Results: N total, N passed, N failed` line from a run of the guarding spec.
Exit 0 is not a pass; a run with no `Results` line is INCONCLUSIVE. That
evidence was not gathered here for any row.

The one class where the citation finding is itself conclusive is the 154
NO_MARKER files with zero markers anywhere plus the 76 FILE_GONE rows: for those
the *scanner hit* is provably dead. The *defect* may not be.

## 5. Recommendation: hand-repair the row set, fix the scanner first

Do **not** regenerate. This is not a prediction — the regeneration was actually
run (§ 3) and measured. It:

1. **Deletes all 99 `blocked`/`done` rows.** The output is 267 rows, every one
   `open`. All 61 `blocked` reasons and all 38 `done` records are gone, along
   with the ~180 hand-authored open rows in the same shape (605-651 etc.).
   Set-differenced, **289 distinct keys present in the current db are absent
   from the regenerated one**, against 25 gained.
2. **Does not fix the duplication.** 267 rows collapse to 166 distinct — 38%
   redundant — with both halves of every mirror pair still walked.
3. **Loses real markers.** 166 distinct found vs 528 distinct comment-form
   markers actually in tracked source: the scanner under-finds by ~3x, on an
   input set 15,100 files *larger* than the correct one.

A regeneration trades a db that is 41% redundant for one that is 38% redundant,
3x incomplete, and stripped of every curated record. That is a strict loss.

Ordered repair:

- **(a) Fix the scanner first — both halves.** Discovery: restrict to tracked,
  non-vendored files and to one canonical member of each mirror pair. Matching:
  find the ~3x gap between its 267 hits and the 713 comment-form markers a plain
  grep finds. Until both land, any regeneration re-inflates *and* under-reports.
- **(b) Split the db by provenance.** Scanner-derived rows and hand-authored task
  rows are different kinds of record and must not share a regenerable table. Only
  the former is safe to regenerate.
- **(c) Re-point the 39 drifted rows** whose file still holds a marker (39 files
  behind 276 NO_MARKER rows) — mechanical, marker text still matches.
- **(d) Triage the 230 provably-dead citations** (154 marker-free files + 76
  FILE_GONE) one at a time, each closure carrying its own `Results:` line.
- **(e) Add the missing markers** — ~528 distinct in source vs ~430 in the db.

## Method — exact commands

Worktree `/mnt/data/worktrees/todo-reconcile` at `e9e22a1230f`, clean.

```sh
# Row extraction (735 rows; greedy .* correctly binds the description because
# file has no quotes and line is numeric)
grep -E '^ +[0-9]+, [A-Z]+,' doc/08_tracking/todo/todo_db.sdn \
 | sed -E 's/^ *([0-9]+), ([A-Z]+), [^,]*, ([^,]*), "(.*)", ([^,]*), ([0-9]+), .*, (open|done|blocked), (true|false) *$/\1\t\2\t\3\t\5\t\6\t\7\t\4/' \
 > rows.tsv     # id, keyword, priority, file, line, status, description

# Citation check, per row: file exists? marker at that exact line? within +/-5?
# (awk driver: test -f; sed -n '<line>p'; match TODO|FIXME|HACK|XXX)

# Clusters
awk -F'\t' '{print $7"\t"$5}' rows.tsv | sort | uniq -c    # -> 374 distinct
awk -F'\t' '{b=$4; sub(/.*\//,"",b); print $7"\x01"$5"\x01"b}' rows.tsv \
 | sort -u | wc -l                                          # -> 430 distinct

# Ground-truth marker census
git ls-files 'src/**' 'test/**' 'scripts/**' 'examples/**' \
 | grep -vE '^src/(compiler_rust/vendor|runtime/vendor)/' \
 | grep -E '\.(spl|shs|rs|c|h)$' > tracked.txt              # 41405
xargs -a tracked.txt -d '\n' grep -H -n -E '(//|#|--|/\*)[[:space:]]*(TODO|FIXME)[:( ]' \
 | wc -l                                                    # 713

# todo-scan (rewrites TODO.md + todo_db.sdn -- back both up first)
cp doc/08_tracking/todo/todo_db.sdn /tmp/before_db.sdn
nohup setsid sh -c 'bin/simple todo-scan > scan.log 2>&1; echo "RC=$?" >> scan.log' </dev/null &
```

`bin/simple` here is the shared Rust seed
`bin/release/x86_64-unknown-linux-gnu/simple` (symlink not rebuilt or replaced).
