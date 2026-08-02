# Verification layer: orphaned guards and dangling references, re-derived

- **Status:** open (two backlogs, both owned below)
- **Measured at:** `66974acc79e754d202c53881eeac08fd86a2a8db`, tree 109,671
- **Date:** 2026-08-02
- **Tooling:** `/usr/bin/grep` pinned throughout (`grep` on this host is ugrep).

This re-derives two counts that were previously INFERRED from a sweep, states
the predicate used for each, and records what was repaired. Every number below
was produced by running the guard, not by estimating.

## Backlog 1 — orphaned guards

**Predicate.** A guard is `scripts/{check,audit}/**.{shs,sh}` plus
`scripts/check-*.shs`. It is ORPHANED when a BFS from the real roots
(`.github/workflows/*`, `scripts/hooks/*`,
`scripts/check/pre-push-conflict-tree-guard.shs`) over broad textual
referrer->basename edges does not reach it. This is
`check-guard-wiring.shs`'s own model, so the number is reproducible by
running it.

| Quantity | At 66974acc | Prior sweep |
|---|---|---|
| Guards total | 422 | 413 |
| Invoked from a hook or CI | 55 | 49 |
| Orphaned | **367** | 364 |
| Listed in `guard_wiring_optout.txt` with a reason | 360 | 364 |
| **Orphaned AND unexcused** | **7** | n/a |

The "~360" figure is CONFIRMED, not refuted: 367 vs 364 is drift from nine
guards added since the earlier measurement. The number that matters for action
is not 367 but **7** — the guards that are orphaned *and* carry no written
reason. The other 360 are declared non-gates (QEMU boots, GPU/DirectX
readbacks, Electron/Bun bitmap captures, FPGA and RISC-V hardware lanes).

### Classification of the 7

| Guard | Class | Disposition |
|---|---|---|
| `check-memory-deallocation-ownership.shs` | dead, CI-capable | WIRED |
| `check-rt-free-abi.shs` | dead, CI-capable | WIRED |
| `check-module-surface-hint-scan-fast-path.shs` | dead, CI-capable | WIRED |
| `check-bootstrap-progress-watch.shs` | dead, CI-capable, **rotted** | WIRED + repaired |
| `check-gpu-runnable.shs` | needs a built `bin/simple` | open |
| `check-utf8-slice-audit-live.shs` | needs a built `bin/simple` | open |
| `stage4-diagnostic-two-phase.shs` | not a gate; a diagnostic corpus sweep | open, likely misfiled under `scripts/check/` |

Four were wired into `.github/workflows/repo-hygiene.yml` (`code-idiom-gates`).
No opt-out line was added and no baseline was touched.

### Truth reveal

`check-bootstrap-progress-watch.shs` was RED against a watcher that works
correctly. Its live-sample assertion ended in `main_log_bytes=3$`, anchoring on
that field being LAST on the line. `bootstrap-progress-watch.shs` later gained
`phase`/`unit_kind`/`done`/`total`/`tasks_*`/`failed`/`cached`/`current`/
`terminal`, moving `main_log_bytes` into the middle of the sample. Nothing ran
the guard, so the drift was never reported.

This is the decay mode of an orphaned guard: it does not merely fail to catch
things, it silently stops being runnable, so wiring it later looks like a
regression. Repaired by matching `main_log_bytes` as a whole FIELD
(`main_log_bytes=3( |$)`), which still rejects `main_log_bytes=30`. Exactness
preserved; only the coupling to field ORDER removed.

### Non-vacuity evidence

Each wired guard was proved live by sabotaging the IMPLEMENTATION it guards —
never a shim — and confirming red, then reverting and confirming green:

| Guard | Sabotage | Result |
|---|---|---|
| bootstrap-progress-watch | watcher stops parsing `milestone` from the state file | FAIL |
| bootstrap-progress-watch | watcher reports a skewed byte count | FAIL |
| bootstrap-progress-watch | stale-PID path exits 0 instead of 3 | FAIL |
| memory-deallocation-ownership | `nogc_sync_mut` arena free call renamed | FAIL |
| memory-deallocation-ownership | `rt_free` widened to two parameters | FAIL |
| rt-free-abi | Cranelift `RuntimeFuncSpec` `rt_free` given arity 2 | FAIL |
| module-surface-hint-scan-fast-path | marker widened to `# Re-exported` | FAIL |

### Refuted hypothesis

`check-workspace-root-guard.shs` (CI-wired) initially appeared FAIL-OPEN: three
undeclared-entry sabotages all returned exit 0. **That was a false positive of
my own scan.** The sabotage files were staged with `git add -N`, which makes
them tracked, and the guard deliberately grandfathers tracked entries outside
`--strict`. Re-run with genuinely untracked files, it fires correctly:

    untracked root file      -> WRG001, exit 1
    untracked src/ child     -> WRG003, exit 1
    untracked test/ child    -> WRG003, exit 1
    clean control            -> exit 0

The guard is live. Recorded because a scan's false-positive rate is a finding:
staging a fixture can silently move it into a guard's grandfathered set.

## Backlog 2 — dangling references

**Predicate.** `check-dangling-references.shs` over tracked `.spl` under `src/`
(vendored trees excluded per CLAUDE.md Owned-Code Scope): a `use` naming a
module no file provides, a `self.foo(...)` defined nowhere, or an imported name
declared by no file at all.

| Category | Count |
|---|---|
| SYMBOL — imported name declared in no src file | 112 |
| MODULE — `use` of a module no file provides | 48 |
| METHOD — `self.foo()` defined nowhere | 13 |
| **Total** | **173** |

The "~171" figure is CONFIRMED. The guard is itself opted out of wiring
(`guard_wiring_optout.txt:69`) because it is red; the backlog was 297 at
`76c3e1e080d`, so it is being driven down.

### False-positive rate: 0%

Re-derived independently by indexing every `fn|class|struct|enum|type|val|
const|me|trait|mixin` declaration across owned `src/**.spl` and intersecting:

    distinct symbols flagged                94
    actually declared somewhere in src       0
    declared nowhere                        94
    false-positive findings           0 / 112  (0.0%)

**These are all real.** PROVED.

### The important split

    imported AND used in the importing file   111 / 112
    imported but never used (safe drop)         1 / 112

This backlog is **not** stale-import cleanup. 111 of 112 are live call sites
against symbols that exist nowhere in the tree. Deleting the imports would
delete working-looking code; implementing 94 missing symbols is a program.
Neither is a silent-fix. Largest cluster: `std.async_core` (12 imports across
`src/lib/nogc_async_mut/async_host/`) — `Poll`, `CancellationToken` and
`TaskState` exist under `src/lib/nogc_async_mut/async/`, but `AsyncError` and
`Priority` exist nowhere in that tier, so the aggregator module cannot be
reconstructed by re-export alone. Target ambiguous; filed, not guessed.

## Backlog 3 — FILE.md manifests (found while checking backlog 2)

All 11 child manifests linked from the root `FILE.md` exist. PROVED. But
`--strict` (grandfathering off) reports **120** tracked entries that no
manifest declares:

| Code | Count | Meaning |
|---|---|---|
| WRG001 | 2 | root entry not allowed by `FILE.md` |
| WRG002 | 19 | immediate root child not declared |
| WRG003 | 99 | entry not declared by its parent manifest |

Concentrated in `doc/06_spec` (55), `test` (11), `scripts` (11), `bin` (9).
These are invisible in normal mode because tracked entries are grandfathered —
enforcement applies only to NEW untracked paths.

**Repaired here:** `src/hardware` and `src/i18n` are tracked directories (30
files, and `src/i18n` is named in CLAUDE.md's structure section) declared by
neither `FILE.md` nor `src/FILE.md`. Both added; WRG003 99 -> 97. Proved by
sabotage: deleting the `i18n` row re-flags it, restoring it clears.

**Also found, not repaired:**

1. Six root-manifest entries name paths that are absent and not gitignored:
   `test/06_fuzz`, `test/07_security`, `test/08_web_platform`, `tools/jupyter`,
   `tools/ref_crypto`, `bin/simple.bootstrap_seed_wrapper.c`. As allowlist
   rows they cause no failure, but they describe a tree that no longer exists.
   Not deleted unilaterally: another lane may be mid-creation, and shrinking an
   allowlist can redden someone else's CI. Needs a decision, not a guess.
2. `check-workspace-root-guard.shs` does not use `git ls-files -z`, so a path
   git must C-quote is prefix-extracted with its opening quote attached. One
   such entry shows up as the bogus root violation `"doc`. A robustness gap in
   the guard, not a tree defect.

## Not done

- The 360 excused orphans were not re-litigated one by one.
- 111 live references to undefined symbols need an owner and a plan.
- The 120-entry manifest backlog needs an owner; do not baseline it.
