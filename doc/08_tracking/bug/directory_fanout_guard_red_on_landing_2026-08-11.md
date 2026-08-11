# Directory fan-out guard was RED on day one (2026-08-11)

Status: RESOLVED (guard GREEN) — with two reorganisations DEFERRED, recorded below.

`scripts/check/check-directory-fanout.shs` landed in `cee8e1fda6be` already
failing, reporting 7 directories over limit against its 2026-08-10 baseline. A
guard that is red on landing trains people to ignore it, so this was cleared the
same night. No file was deleted to make a count pass.

## Per-offender disposition

| directory | HEAD | baseline | disposition |
|---|---|---|---|
| `doc/08_tracking/bug` | 2421 | 2413 | **EXEMPT** — append-only auto-generated tracker; `.claude/rules/structure.md` marks `doc/08_tracking` DO NOT REFACTOR |
| `doc/09_report` | 805 | 804 | **EXEMPT** — append-only auto-generated temporal reports; same DO NOT REFACTOR marking |
| `scripts/check` | 585 | 583 | baseline 583→585 — the +2 is the fan-out guard's **own** two files (`check-directory-fanout.shs`, `directory_fanout_baseline.txt`) |
| `src/compiler/00.common` | 36 | 35 | baseline 35→36 — the +1 is `module_path_naming.spl` (`3e7547b5175`). Split DEFERRED, see below |
| `src/lib/nogc_sync_mut/spec/evidence/counterpart` | 13 | 11 | baseline 11→13 — `cipher_sha256_provider.spl`, `dynlib_provider.spl`. Split DEFERRED, see below |
| `src/os/drivers/gpu/board_vulkan` | 18 | (new) | new baseline entry at 18. Split DEFERRED, see below |
| `test/01_unit/os/vulkan` | 12 | (new) | new baseline entry at 12. Split DEFERRED, see below |

Nothing was moved. Every numeric entry still fails on **further** growth, so
none of these is laundered — only the two generated trees are silenced.

## Why no reorganisation was performed

**`board_vulkan` / `test/01_unit/os/vulkan` are mid-flight.** Measured
2026-08-11 05:00Z: four `backend_*.spl` modified 7 minutes earlier, three
`encoder_*.spl` plus four specs **staged in the shared index** by a concurrent
session, and 6 further untracked files. Moving them would clobber another
session's in-flight work and its staged index — see
`feedback_dont_touch_a_file_another_concurrent_session_is_midflight_on`.

**`counterpart` is imported by exactly those mid-flight files.** A
`providers/` split (the obvious remedy: 6 `*_provider.spl` out, leaving 7) needs
14 importer edits, several of them inside `board_vulkan`. Same clobber risk, and
an unresolved `use` only WARNs, so a broken import would not fail loudly.

**`00.common/module_path_naming.spl`** has 4 importers across compiler layers
20/50/70/80. Moving one file into a new one-file subdirectory is worse structure
than leaving it, and compiler-layer moves under six-session contention are the
same risk class.

## The local working copy understated it: origin was at 30, not 7

The 7 above are what the guard reports against the local (divergent, older)
`HEAD`. Measured against the actual `main@origin` tip `b6d717e62e2` the same
night, **30** directories are over — the extra 23 are almost all `test/**`
directories that other sessions grew by landing new specs in the ~24h since the
baseline was taken (`test/01_unit/compiler/driver` 74→78,
`test/01_unit/lib/common` 379→383, `scripts/check` 585→600, …), plus one new
directory `src/os/kernel/arch/common` at 13.

All 30 are reconciled to their measured `main@origin` counts in this commit.
None is a fan-out *design* problem: they are directories that were already
known violations and that grew by ordinary spec authoring. Every entry still
fails on further growth.

**Known limitation, stated rather than engineered around:** a per-count
baseline over the live test trees goes red again within hours, because several
sessions add specs continuously. That is the guard working as designed
(fan-out IS growing), but it means this guard needs a periodic reviewed
reconciliation, exactly like `test_tree_divergence_baseline.txt`. Do NOT
respond to that by exempting `test/**` — exemption is for append-only
*generated* trees only. Reconcile, or split.

## Follow-up (do these when the vulkan work quiesces)

1. Split `src/os/drivers/gpu/board_vulkan` by topic —
   `backends/`, `encoders/`, `boundary/`, `corpus/`, `providers/` — and mirror the
   spec split under `test/01_unit/os/vulkan`. **Mirror across BOTH `test/01_unit/`
   and `test/unit/`** or `check-test-tree-divergence.shs` hard-blocks the push.
   (`test/unit/os/vulkan` does not currently exist.)
2. Split `src/lib/nogc_sync_mut/spec/evidence/counterpart` into
   `counterpart/providers/`, updating all 14 importers and verifying by
   **running** `test/01_unit/infra/counterpart/*_spec.spl`, not by absence of
   errors.
3. Shrink the corresponding baseline entries in the same commit.

## Guard change

`EXEMPT` support was added to the baseline format:
`path<TAB>EXEMPT<TAB><mandatory reason>`. An exempt directory is never reported
at any size. It is for append-only auto-generated trees ONLY — hand-authored
code gets a reviewed numeric baseline or a split. The guard now also validates
every baseline line and exits **2** (`ERROR — nothing was checked`) on a
malformed one, so an `EXEMPT` with no reason cannot be smuggled in. There is
still **no** `--generate-baseline` flag.

## Fail-closed proof (2026-08-11)

Against a plumbing-built commit off HEAD adding one file to `scripts/check`
(585→586) and 11 files to a never-baselined `src/zz_fanout_proof_dir`:

```
FAIL — 2 over limit: src/zz_fanout_proof_dir,scripts/check      exit 1
```

An `EXEMPT` line with no reason:

```
ERROR — nothing was checked (malformed baseline)                exit 2
```

Both proof artifacts removed; baseline byte-identical afterwards
(`diff -q` clean, no `zz_` residue in `git status`). Guard then:

```
PASS — 18675 director(ies) checked, 0 over limit                exit 0
```
