# Guard vacuity audit — scripts/check/ (2026-08-23)

Row §27, `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md`.

Audits every script in `scripts/check/` for the defect class that bit three
times on 2026-08-22/23: a guard that emits a green verdict without having
examined the population it claims to cover.

- `check-cow-alias-hotpath.shs` hardcoded `SRC="$ROOT/src/compiler"`; `src/lib`
  was never scanned. Reported `PASS … 7 offender(s)`; the tree held 219. Fixed `50a379f83b7`.
- `check-untyped-return-value.shs` treated any signature containing `) ->` as
  already-typed, skipping every callback-taking function in the tree. Fixed `da90106fcd6`.
- `check-type-walk-constructor-parity.shs` was deleted as collateral of a revert
  while its bug record still claimed enforcement. Re-landed `0fe0323565c`.

Base commit: `74f2b254081`. Method: static classification of all 768 `.shs`
files on the five axes, plus an **empirical empty-tree sweep** — 451 guards
short enough to run were executed against a tree containing nothing but a `.git`
dir and empty `src/`, `test/`, `doc/`; any exit 0 is a vacuous pass by
definition. Exit codes were read directly into a variable, never through a pipe
(a pipeline's `$?` is `tail`'s, and that alone produced a false `rc=0` twice
during this audit).

## Population summary (768 guards)

| Axis | Measured |
|---|---|
| Has `--selftest` | 152 / 768 (19.8%) |
| Selftest with a MUST-FAIL fixture | 78 / 768 (10.2%) — half of those that have one |
| Emits the `ERROR — nothing was checked` / exit 2 convention | 254 / 768 (33.1%) |
| Emits `PASS` with no zero-item guard at all | 193 |
| Static fail-open pattern (missing tool/artifact ⇒ success) | 18 |
| Uses a baseline/allowlist | 40, of which **12 never check for staleness** |
| **Empirically PASSed an empty tree** | **36 of 451 tested** |

The 36 is a floor, not a total: guards exceeding the 25s sweep timeout were not
counted, and the 317 guards too long to sweep were not tested at all.

## Ranked findings

### R1 — CRITICAL: documented-MANDATORY guards are wired to nothing

`.claude/rules/vcs.md` states of five guards, verbatim, "Wired into
`pre-push-conflict-tree-guard.shs` alongside the other guards", and labels
several MANDATORY. The actual enforcement surfaces are the must-check ledger
`doc/08_tracking/check/must_check_db.sdn` (via `check-push-must-pass.shs`, which
the hook `exec`s), `rules.sdl`, and `.github/workflows/`. Measured presence:

| Guard | ledger | rules.sdl | CI |
|---|---|---|---|
| `check-c-runtime-compiles-push.shs` | 0 | 0 | 0 |
| `check-runtime-api-regression-push.shs` | 0 | 0 | 0 |
| `check-unbacked-extern-ratchet.shs` | 0 | 0 | 0 |
| `check-no-direct-rt.shs` | 0 | 0 | 0 |
| `check-stage-binaries-runnable.shs` | 0 | 0 | 0 |
| `check-cow-alias-hotpath.shs` (fixed today) | 0 | 0 | 0 |
| `check-untyped-return-value.shs` (fixed today) | 0 | 0 | 0 |
| `check-type-walk-constructor-parity.shs` (re-landed today) | 0 | 0 | 0 |

This is defect #3 at scale: the guards work and discriminate, but nothing runs
them while the rules file asserts they gate every push. A guard nobody invokes
has the same effect as one that always passes, and is harder to notice because
it looks healthy when run by hand.

Corroborated independently by the repo's own meta-guard: `check-guard-wiring.shs`
reports **`FAIL — 871 guard(s) checked, 414 unwired`** (exit 1) against an
opt-out file holding 343 entries. It has been honestly RED and ignored; its own
seeded baseline was 364 orphans, so the population has grown by 50.

### R2 — HIGH: vacuous passes confirmed by execution (36)

Guards that exited 0 having scanned an empty tree. The source-ratchet subset is
the dangerous one — these are real invariants over real populations:

| Guard | Empty-tree verdict |
|---|---|
| `check-core-lib-purity.shs` | `core_purity_ok=true` — **FIXED, see below** |
| `check-seed-extern-registry.shs` | `seed_extern_registry_mode=informational (no baseline; exit 0)` — **FIXED, see below** |
| `check-cpu-hotloop-idiom.shs` | `cpu_lane_hotloop_ok=true` — its own header at line 90 warns of exactly this shape and it happens anyway |
| `check-ui-backend-isolation.shs` | `ui_backend_isolation_ok=true` |
| `check-runtime-symbol-lane-divergence.shs` | `runtime_symbol_lane_divergence_ok=true` |
| `check-type-name-collisions.shs` | `no enum-vs-struct/class name collisions found` |
| `check-crypto-verify-symbol-collisions.shs` | `OK (all guarded symbols uniquely defined)` |
| `check-rendering-source-coupling.shs` | `STATUS: PASS` |
| `check-riscv-rtl-truth.shs` | `riscv_rtl_truth_ok=true (nothing to check)` — states its own vacuity and returns 0 anyway |

A second subset launders an **environment SKIP into exit 0** — absence of
evidence returned as evidence of absence: `check-electron-vulkan-web-parity.shs`
(electron not installed), `check-runtime-https-provider.shs`
(`SIMPLE_RUNTIME_WM_PATH` unset), `check-gpu-runnable.shs` (no `bin/simple`),
`check-scilib-accelerator-gates.shs`, `check-x25519mlkem768-metal-ntt.shs`,
`check-native-parity-if-selfhosted.shs` (which prints `SKIPPED (not measured;
not a pass)` and then exits 0 — the text is right and the exit code contradicts
it), `sync-native-health-guard.shs` (`no compiler delta, skip`),
`normalize-line-endings.shs` (`no staged files to check`).
The house rule these violate is already written down in `.claude/rules/vcs.md`
for `check-c-runtime-compiles-push.shs`: a machine with no compiler is ERROR,
never a pass.

### R3 — MEDIUM: selftests that prove nothing

Only 152 of 768 guards have `--selftest`, and only 78 of those contain a
must-fail fixture. **74 guards ship a selftest built entirely from must-pass
fixtures**, which proves the script runs, not that it discriminates. Both
guards fixed in this change previously had no selftest at all.

### R4 — MEDIUM: one-directional and stale baselines

40 guards carry a baseline/allowlist; **12 never test for staleness**, so a
baselined entry that has since been cleaned keeps the ratchet permanently loose.
`check-core-lib-purity.shs` was worse than silent — it *printed*
`core_purity_baseline_stale=` and exited 0 anyway.

Two ratchets are honestly RED and being stepped over rather than acted on:

- `check-no-new-fail-open.shs` — `FAIL — 4414 site(s) checked, 377 new fail-open`
- `check-no-silent-fail-open.shs` — `FAIL — 7096 site(s) checked, 89 NEW fail-open (baselined: 805)`

Not regenerated here: absorbing 466 sites would hide new debt, which the audit
brief forbids.

### R5 — the pipeline `$?` trap

Not a guard defect but the reason several were mis-scored during this audit:
`sh guard.shs | tail -2` reports `tail`'s status, so a guard printing `FAIL`
reads as `rc=0`. `check-guard-wiring.shs` and `check-seed-extern-registry.shs`
both appeared green through a pipe and are exit 1 when measured directly. Any
orchestrator that pipes a guard into `tail`/`grep`/`head` without `set -o
pipefail` is a silent fail-open.

## Fixed in this change

### `check-seed-extern-registry.shs` (`ea2494f9ef5`)

- **Scope blindness.** Scanned only `src/compiler` (287 `extern fn rt_*` names),
  justified by a header claim that "only `src/compiler` is load-bearing". False:
  per `.claude/rules/commands.md` the stdlib is read as SOURCE on every process
  start (82 opens of `src/lib/**.spl`, zero `.smf`), so the seed interprets
  stdlib externs on the same path. `src/lib` holds **2,097** such names, of which
  **632 are unregistered** — 7.3x the scanned population, entirely invisible.
  `src/lib` is now a second GATED section, frozen in
  `scripts/check/seed_extern_lib_baseline.txt`. Scanned population **287 → 2,384**.
- **Vacuous pass.** Empty tree gave `informational (no baseline; exit 0)`, rc 0.
  Zero declarations, zero registry tokens, or a missing baseline is now
  `ERROR — nothing was checked`, exit 2.
- **Staleness** is now two-directional, and a fatal `--selftest` was added:
  7 fixtures, 4 MUST-FAIL (including one replaying the `src/lib` scope hole) and
  3 MUST-ERROR.
- Baselines are **deletions-only**: the compiler baseline drops 84 now-registered
  entries (177 → 93) and keeps the 2 genuinely-new names (`rt_smf_reader_`,
  `rt_text_eq_any`) unabsorbed, so the guard stays honestly RED on them exactly
  as before.
- **Discrimination proved.** Empty tree `rc 0 → rc 2`; real tree
  `FAIL — 2384 extern(s) checked, 2 new unregistered` rc 1; selftest 7/7.

### `check-core-lib-purity.shs` (`2976d1e694b`)

- **Vacuous pass.** Counted what it found, never what it looked at; a tree with
  no `src/lib/common` gave `core_purity_ok=true` rc 0. A scan below
  `CORE_PURITY_MIN_FILES` (50, against a real 933) or an absent core tier is now
  ERROR exit 2. Measured `rc 0 → rc 2`.
- **Missing tool ⇒ pass.** Both scans were `rg … 2>/dev/null || true`, so a host
  without ripgrep produced a green verdict. `rg` is now required, and its status
  is captured directly on the line after the call with its 0/1/>1 tri-state
  honoured.
- **One-directional ratchet.** A stale baseline entry was printed and ignored;
  it is now a FAIL.
- Fatal `--selftest`, 7 fixtures (3 must-fail, 3 must-error, 1 must-pass).
- No baseline regenerated: the guard was already RED on 18 unbaselined
  violations and reports the same 18, plus the 1 stale entry it used to swallow.
- **Discrimination proved.** Empty tree ERROR rc 2; real tree
  `FAIL — 933 file(s) scanned, 18 new violation(s), 1 stale baseline entry` rc 1.

## Recommended next, in order

1. **R1 is the highest-value remaining item** and is not a code fix: either wire
   the eight guards into `must_check_db.sdn` / `rules.sdl` / CI, or correct
   `.claude/rules/vcs.md` to stop asserting enforcement that does not exist.
   Leaving both as they are is the worst of the three states.
2. Apply the same non-vacuity + must-fail-selftest treatment to the seven
   remaining R2 source ratchets, `check-cpu-hotloop-idiom.shs` first (its header
   already names the hazard).
3. Convert the environment-SKIP subset from exit 0 to exit 2.
4. Act on `check-guard-wiring.shs`'s 414 unwired guards rather than continuing
   to step over its RED.

## Reproducing

The empty-tree sweep is the cheapest way to re-derive R2:

```sh
mkdir -p /tmp/empty/scripts/check /tmp/empty/src && (cd /tmp/empty && git init -q)
cp -r scripts/check/. /tmp/empty/scripts/check/
( cd /tmp/empty && timeout 25 sh scripts/check/<guard>.shs ) >/tmp/o 2>&1; echo "rc=$?"
```

`rc=0` is a vacuous pass. Never read the status through a pipe (R5).
