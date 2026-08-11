# Feature Expert — rules.sdl / LLM fraud prevention

**Canonical meaning.** `rules.sdl` (repo root) is the registry of counts, files, lists,
and lanes this repo promises to keep. Its single invariant: coverage may grow freely
and may never shrink without a reviewed, recorded decision.

**Implementation.**
- `rules.sdl` — the registry. Gate fields: `id`, `group`, `cmd`, `min`, `status`.
- `scripts/check/check-rules-sdl.shs` — evaluates gates. `--group quick|full`,
  `--ref <commit>`, `--selftest` (5 fixtures, fatal, runs before every scan).
- `scripts/check/check-rules-sdl-integrity.shs` — the registry may not shrink to
  escape the registry. `--selftest` (2 arms).
- Wiring: `scripts/check/pre-push-conflict-tree-guard.shs` (quick),
  `src/app/cli/bootstrap_check.spl` check 9 (full), `scripts/hooks/pre-commit`
  (integrity only).

**Use for.** Deciding whether a change is allowed to reduce test/script/lane coverage,
and proving it did not.

**Do not substitute.** This is not a replacement for the four mandatory pre-push guards
(conflict tree, conflict markers, tree size, test-tree divergence). Those check that the
tree is STRUCTURALLY sound; none of them notices a tree that is intact but has fewer
tests in it. Different failure, different guard.

**Primary guide.** `doc/07_guide/infra/llm_fraud_prevention.md`
**Plan.** `doc/03_plan/infra/llm_fraud_prevention/rules_sdl_anti_fraud_plan.md`

## Expert notes — things that cost time here

**Baseline the gate with the gate's own command.** Baselines derived from
`git ls-files` (working copy) while the gate reads `git grep`/`git ls-tree` at a commit
compare two different populations. This produced a 4-file phantom shrink on the very
first run: the working copy had uncommitted markdown the gate could never see. Always
derive `min` by running the gate's `cmd` at `HEAD`.

**Counts drift upward under concurrent sessions.** Between two measurements minutes
apart, `spec_files` moved 14056 → 14057 and `check_scripts` 531 → 534 because other
sessions landed commits. That is why gates are floors, not equalities — never "fix" a
gate by pinning an exact number.

**`grep -c` with an `|| echo 0` fallback emits TWO zeros.** `grep -c` prints `0` AND
exits 1 on no-match, so the fallback appends a second line and every downstream
arithmetic test dies with "Illegal number". Count with `awk '/^ok$/{n++} END{print n+0}'`.
The guard's own selftest caught this — which is the argument for the selftest.

**A tombstoned removal legitimately lowers the gate count.** The integrity guard must
compute `allowed_min = base_n - recorded_removals` before comparing, or every correctly
recorded removal trips the raw count check. Selftest arm 2 exists precisely for this.

**Zero evaluated gates is ERROR, not PASS.** The most common guard defect in this repo
is checking nothing and exiting 0. Fixture 4 of the selftest pins this behavior; do not
"simplify" it away.

**`status: planned` may never report PASS.** A declared-but-unbuilt lane prints
`SKIPPED — ... NOT VERIFIED` and is counted separately in the summary. A planned lane
silently counted as passing would make the registry itself a fraud vector.

**Enforcement reality.** `pre-commit` is not installed in this clone and jj bypasses git
hooks entirely. Treat pre-push and bootstrap as the only load-bearing local gates;
anything relying on pre-commit alone is advisory.

## Sabotage record (2026-08-11)

Required three numbers for the count gate, measured by building scratch commits with
git plumbing (no HEAD movement):

| arm | result |
|---|---|
| pre-sabotage | `PASS — 10 gates checked, 0 shrank` |
| sabotaged (200 specs deleted from the tree) | `FAIL — spec_files: 13857 < min 14056 — SHRANK by 199` |
| reverted | `PASS — 11 gates checked` (full group) |

The arm bites. Re-run it after any change to the parsing or tally logic.

## Lane wiring notes (2026-08-11, all 18 gates green)

**Scenario/list lanes report a verdict LINE, not a count.** Each such gate encodes it
for the same numeric mechanism the count gates use: `2` = PASS, `1` = SKIPPED,
`0` = anything else, with `min: 1` where hardware may be absent and `min: 2` where it
may not. Do not add a second code path for these — the encoding is the whole trick.

**Two guard scripts refuse to guess their arguments, and a bare call is an ERROR, not
a pass.** `check-lint-census.shs` needs targets; `check-seed-builds-push.shs` needs an
explicit range (`$REF~1..$REF`). Both were initially wired bare, both went red, and
that was correct behavior — fail-closed caught my own miswiring.

**The lint gate is the CLASSIFIER self-test, not a tree census, and says so.** A real
census is not gate-shaped: `simple lint` costs ~11.7s startup + ~3.3-4.0s per function
decl, superlinear (~119s for a 120-line file). Gating the classifier still catches the
failure that would make every census silently wrong.

**Sabotage the implementation, not the spec's input.** For `pixel_region_width` the arm
was breaking the accessor in `model.spl` (high half → low half): PASS 4/4 → FAIL 3/4 →
revert → PASS 4/4. Restore from a backup whose line count you verified BEFORE using it
as the restore source — a truncated backup silently destroys the file you are proving.

## Open work

- **Background `.smf` compile cache**: NOT built, deliberately. The dynSMF lane
  (`src/os/smf/dynsmf_session.spl`, `src/app/startup/dynsmf_autoload.spl`) already does
  background-compile-then-cache. Wire the interpreter run path to it; do not build a
  second mechanism. Checked autoload must stay fail-closed until a valid `SMF\0`
  artifact exists — never load a partial one.
- **Two lanes are SKIPPED on this host** and have never been seen green: `qemu_boot_hello`
  (needs `bin/release/x86_64-unknown-simpleos/simple`; QEMU and OVMF are present) and
  `fpga_rv_linux` (needs the KV260). Their transcript bars are selftest-calibrated, but
  a calibrated bar is not a passing lane — do not claim either as covered.
- **db SIMD dispatch** is detected but not activated (`simd_active: false`). Wiring it
  means updating `webdb_simd_accel_system_spec.spl` deliberately, with evidence.
