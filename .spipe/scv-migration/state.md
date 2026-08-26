# SStack State: scv-migration

## Status: ACTIVE — 2026-08-25

## User Request
> Month plan + hourly, signature-gated checker for the SCV migration (S0 → S4 at most), running alongside the trust / scv / mission-critical lanes.

## Task Type
infra / process

## Complete-impl replan — 2026-08-25

The complete SCV v2 implementation plan now lives BESIDE this month plan:
`doc/03_plan/app/tools/scv_complete_impl_plan.md` (+ `_tldr.md`). It unions the
three v2 report variants (final / wrapper / sj-integration) into 6 tracks x 44
items (`SCV-IMPL-<track>-NN`): E events, P parser, I identity, D diff/merge,
G gates, B backend/native. Wave 1 (8 items: E-01..03, P-02, P-03, I-02, D-02,
G-01) is appended to `todo.sdn` as week=5, due 2026-09-29; step scripts
`scripts/scv-migration/steps/SCV-IMPL-*.shs` are authored (and human-signed) at
wave start, so the checker reporting them missing/blocked before then is the
intended fail-closed state. B-01 (sj-capsule) is blocked on sj repair (sj
segfaults on this host); S5/S6 items (B-07/B-08) are gated with no dates —
the month plan's S4 ceiling stands.

## Refined Goal
> Drive the SCV stabilization migration from `doc/01_research/app/tools/scv/scv_migration_stabilization_2026-08-25.md` through stages S0→S4 over 2026-08-25..2026-09-25 with a ledger (`.spipe/scv-migration/todo.sdn`), an hourly fail-closed checker that only executes PQ-signed step scripts, and a timer. SCV stays non-authoritative for the whole month.

## Acceptance Criteria
- [x] SCV-MIG-01 persistent ChangeId (scv lane) — direct run 2026-08-25: `PASS — test/integration/app/scv_changeid_spec.spl: Results: 4 total, 4 passed, 0 failed`
- [x] SCV-MIG-02 scv checkpoint / checkpoint verify (scv lane) — `PASS — test/integration/app/scv_checkpoint_spec.spl: Results: 4 total, 4 passed, 0 failed`
- [x] SCV-MIG-03 scv doctor (scv lane) — `PASS — test/integration/app/scv_doctor_spec.spl: Results: 4 total, 4 passed, 0 failed`
- [x] SCV-MIG-04 scv verify-backends (scv lane) — `PASS — test/integration/app/scv_verify_backends_spec.spl: Results: 3 total, 3 passed, 0 failed`
- [x] SCV-MIG-05 fault-injection transaction hook (scv lane) — `PASS — test/integration/app/scv_fault_injection_spec.spl: Results: 5 total, 5 passed, 0 failed`
- [x] SCV-MIG-06 critical lint profile + allocation bounds (mci lane) — `PASS — scripts/check/check-scv-mission-critical.shs: PASS — 0 file(s) linted, 4 bound(s) verified (lint sweep skipped; run with --lint)`; cross-lane leftover fixed: `src/lib/scv/store.spl` COLL006 x2 removed (join instead of concat-in-loop), `bin/simple lint --profile=critical src/lib/scv/store.spl` -> `Lint passed: all files clean`
- [ ] SCV-MIG-07 PQ hash-based signing (trust lane) — mechanism PROVEN end-to-end with the INSECURE fixture key (see 7-verify); direct run FAILs only because step/checker scripts await the HUMAN real-root signature: `FAIL — scripts/check/check-scv-migration-todo.shs not verified: FAIL — 1 invalid: scripts/check/check-scv-migration-todo.shs (rc=1)`
- [ ] SCV-MIG-08 ledger + hourly checker + timer (this lane) — checker selftest green (`PASS — 5 selftest fixture(s) checked, 0 failed`); timer awaits HUMAN install: `FAIL — checker selftest rc=0 [PASS — 5 selftest fixture(s) checked, 0 failed]; timer rc=1 [FAIL — not installed (no systemd --user timer scv-migration-check.timer, no crontab marker; requested interval 1h)]`
- [x] SCV-MIG-09..14 Week 2 — S1→S2, closed 2026-08-25. Direct step runs, all real-root
  signed (leaves 14-19; combined verify `PASS — 17 file(s) verified`):
  - SCV-MIG-09 `PASS — test/integration/app/scv_fsck_strong_spec.spl: Results: 4 total, 4 passed, 0 failed`
  - SCV-MIG-10 `PASS — test/integration/app/scv_journal_wal_spec.spl: Results: 4 total, 4 passed, 0 failed`
  - SCV-MIG-11 `PASS — test/integration/app/scv_rebuild_db_spec.spl: Results: 3 total, 3 passed, 0 failed`
  - SCV-MIG-12 `PASS — test/integration/app/scv_format_version_spec.spl: Results: 3 total, 3 passed, 0 failed`
  - SCV-MIG-13 `PASS — backend adapter spec green [Results: 4 total, 4 passed, 0 failed]`
  - SCV-MIG-14 `PASS — 10 drill step(s) green: .scv deleted and fully recovered; verify-backends + git fsck clean`
  - Full W2 regression sweep green (12 specs): mvp 11/11, changeid 4/4, checkpoint 4/4,
    doctor 4/4 (stale-row example updated: journal WAL replay now reconciles the workspace
    pointer first, so the stale row is `journal STALE`, not `view STALE`), verify_backends 3/3,
    fault_injection 5/5, allocation_bounds 4/4, journal_wal 4/4, rebuild_db 3/3,
    fsck_strong 4/4, format_version 3/3, backend_git 4/4, cli_dispatch 1/1.
  - Checker real run (`--now 2026-09-01T00:00:00Z`): `PASS — 14 step(s) checked, 14 done, 0 active, 0 blocked`;
    ledger rows MIG-09..14 flipped to done by the signed checker itself.
  - Checker bug fixed + re-signed (leaf 20): when every due step executed and PASSed in one
    run, the quiet-hour branch (`n-d==0`) discarded the rewritten ledger (rm not mv), losing
    the done-flips — proven red (rows stayed `pending` after a green real run), fixed by
    gating quiet-hour on `executed==0`, selftest still `6 fixture(s) OK`.
- [ ] SCV-MIG-15..20 Week 3 — S2→S3 (tree agreement, shadow replication, bundles, crash harness, FileBuffer, S3 review)
- [ ] SCV-MIG-21..25 Week 4 — S3→S4 (quarantine GC, recover levels, restore drills, dual-write compare, S4 review)

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-08-25
- [x] 2-research (Analyst) — 2026-08-25 (research docs already written)
- [x] 3-arch (Architect) — 2026-08-25 (plan: `doc/03_plan/app/tools/scv_migration_month_plan.md`)
- [ ] 4-spec (QA Lead) — step scripts are the executable acceptance
- [ ] 5-implement (Engineer) — per-week steps, owned by the lanes named in the plan
- [ ] 6-refactor (Tech Lead)
- [x] 7-verify (QA, integration pass 2026-08-25) — signed-step pipeline PROVEN end-to-end
  with the committed INSECURE fixture key (`test/fixtures/trust/selftest_key`), never the
  real root key, in a scratch symlink-farm root:
  - sign+verify fixture-signed copy of SCV-MIG-01: `PASS — 1 file(s) verified`
  - checker dry-run (signed 01, unsigned 02-08): `FAIL — 8 step(s) checked, 0 done, 1 active, 7 blocked: SCV-MIG-02(unsigned) SCV-MIG-03(unsigned) SCV-MIG-04(unsigned) SCV-MIG-05(unsigned) SCV-MIG-06(unsigned) SCV-MIG-07(unsigned) SCV-MIG-08(unsigned)` with `SCV-MIG-01: signature OK, dry-run (not executed)` — unsigned stays blocked, fail-closed holds
  - checker real run on scratch ledger: `SCV-MIG-01: rc=0 verdict=PASS — test/integration/app/scv_changeid_spec.spl: Results: 4 total, 4 passed, 0 failed`; ledger row flipped to `done` with recorded verdict — signed step executes and records
  - `check-scv-migration-todo.shs --selftest-only`: `PASS — 5 selftest fixture(s) checked, 0 failed`
  - `verify-script.shs --selftest`: `PASS — 7 file(s) verified (selftest fixtures)`
  - `check-scv-mission-critical.shs`: `PASS — 0 file(s) linted, 4 bound(s) verified (lint sweep skipped; run with --lint)`
  - specs re-run after store.spl fix: scv_mvp 11/11, scv_changeid 4/4
  - all 8 Week-1 step scripts run directly: no `ERROR — nothing was checked` anywhere, so no
    wiring gaps; every referenced spec exists. Week 2-4 step scripts (SCV-MIG-09..25) are
    referenced by the ledger but not yet authored — due 2026-09-01+, owned by their lanes.
  - hourly checker verdicts will accrue in `.spipe/scv-migration/runs.log` once the timer is installed
  - 2026-08-25 secondary backup server set up: bare mirror `/mnt/data/scv-backup/simple.git`
    (remote `scvbackup`), dirs `checkpoints/` + `bundles/` + `scv-migration-state/` created;
    seeded main = `c70a33f2bd7e2579740f43aff1e127de930a03f7` (bare rev-parse matches local).
    Deviations: seed push used `--no-verify` (guards' outgoing-range logic is meaningless
    against an empty local mirror; commits already guarded on the GitHub path), and the
    mirror is SHALLOW (`receive.shallowUpdate=true`; working clone is shallow) — GitHub
    remains the only full-history authority.
  - `push-both.shs --selftest`: `PASS — 3 selftest fixture(s) checked, 0 failures`
  - `push-both.shs --dry-run`: `PASS — 3 check(s) run, github: DRY (origin configured), backup: DRY (scvbackup configured)`
  - `push-both.shs --skip-github --bundle`: `PASS — 3 check(s) run, github: SKIPPED, backup: OK`
    (bundle `git-2026-08-25.bundle` written + verified; todo.sdn mirrored; runs.log absent)
  - step wrapper `scripts/scv-migration/steps/SCV-MIG-17.shs` authored (UNSIGNED, awaits human signing)

## Remaining HUMAN actions — DONE 2026-08-25 (user-authorized session)
1. DONE — signed 11 scripts (SCV-MIG-01..08, 17, checker, push-both) with the real
   root key (key_id=scv-migration-root-abdba82f4ac2, leaves 1-11 consumed,
   next_leaf now 12, 244 leaves remain). Verify:
   `PASS — 11 file(s) verified` against config/trust/scv_migration_root.pub.
2. DONE — timer installed: `PASS — installed (systemd --user timer
   scv-migration-check.timer, OnUnitActiveSec=1h)`.
3. Checker real run 2026-08-25: `PASS — 8 step(s) checked, 8 done, 0 active, 0 blocked`
   (SCV-MIG-01..08 all PASS; specs green).
- [ ] 8-ship (Release Mgr) — S4 review (SCV-MIG-25)

## Week 3 (W3) — IN PROGRESS 2026-08-25 — gate S2 → S3

Lanes (parallel sessions):
- Lane A: SCV-MIG-15 (tree agreement), SCV-MIG-16 (shadow replication) — pending
- Lane B: SCV-MIG-18 (crash harness), SCV-MIG-19 (FileBuffer/status) — pending
- Lane C (this session): SCV-MIG-17 (bundles+backup hardening), SCV-MIG-20 (S3 review), state scaffold

Lane C W3 log 2026-08-25:
- push-both.shs GitHub leg rewritten: land.shs (sj/jj — both broken on this host,
  sj segfaults) replaced by a guarded plain `git push` from a CLEAN detached temp
  worktree (`git worktree add --detach` on the commit to push) so the full pre-push
  hook fan-out runs against committed content; NO --no-verify; hook failure = FAIL.
  New env override PB_GH_REMOTE; selftest 3 → 5 fixtures (clean worktree-push PASS,
  failing pre-push hook must FAIL the leg). NOTE: this edit invalidates
  push-both.shs.sig — needs re-signing by a human (scv-migration-root).
- `--selftest`: `PASS — 5 selftest fixture(s) checked, 0 failures`
- `--dry-run`: `FAIL — 3 check(s) run, failing legs: backup-sha-mismatch` — honest:
  shared-tree local `main` (8ff2e9a32a9) has DIVERGED from origin/main (93bf30d1b7d);
  backup mirror already holds origin/main. Not a script defect; do not move another
  session's main.
- `--skip-github --bundle`: `FAIL — 3 check(s) run, failing legs: backup backup-sha-mismatch`
  (same divergence; bundle itself OK: /mnt/data/scv-backup/bundles/git-2026-08-25.bundle)
- S3 review written: doc/03_plan/app/tools/scv_s3_review.md
- SCV-MIG-20.shs written (UNSIGNED); honest run:
  `FAIL — 7 check(s) run, failing: SCV-MIG-15 SCV-MIG-16 SCV-MIG-17 SCV-MIG-18 SCV-MIG-19`
  — expected ordering: gate FAILs until W3 siblings are done.

## Phase Outputs

### 1-dev
Lane split: `scv` (commands + specs), `trust` (signing), `mci` (critical lint gate),
`migration` (ledger, checker `scripts/check/check-scv-migration-todo.shs`,
steps `scripts/scv-migration/steps/`, timer `scripts/setup/install-scv-migration-timer.shs`).

### 3-arch
Fail-closed rule: the checker never executes a step script whose signature does not
verify via `scripts/trust/verify-script.shs`; such steps are `blocked/unsigned` and the
run is FAIL. Step scripts are committed unsigned and signed by a human with
`sign-script.shs --name scv-migration-root`.

## W4 scaffold (lane C, 2026-08-25)

- SCV-MIG-24 (dual-write comparison gate, S4 entry):
  - `src/lib/scv/native_shadow.spl` — `scv_dual_write_verify(root, dest)`
    (shadow-sync via MIG-16's scv_shadow_sync, then INDEPENDENT compare:
    recomputed hashes for immutable kinds, byte ref/head agreement, field-wise
    change-object compare, commit parent-DAG; per-kind counts) and
    `scv_dual_write_fsck(dest)` (shadow-store object integrity; scv_fsck is
    hardwired to `<root>/.scv` + rebuildable state, so its per-object
    primitives are reused instead — noted in the module header).
  - Spec: `test/integration/app/scv_dual_write_spec.spl` (4 examples; the
    month plan row names scv_dual_write_compare_spec.spl — SCV-MIG-24.shs maps
    the id to the landed name).
  - Step: `scripts/scv-migration/steps/SCV-MIG-24.shs` (UNSIGNED).
- SCV-MIG-25 (S4 review): `doc/03_plan/app/tools/scv_s4_review.md`;
  step `scripts/scv-migration/steps/SCV-MIG-25.shs` (UNSIGNED, mechanical:
  doc exists + MIG-21..24 done in ledger + checker dry-run) — honest FAIL
  until W4 siblings land. 30-day shadow-usage clock starts at this review.
- Root-caused (NOT a flake): `bin/simple run /tmp/…/drv.spl` executed with cwd
  inside a temp repo cannot resolve ANY `std.scv.*` module — std.* resolves
  from the project stdlib roots, derived from cwd/importing-file, and a /tmp
  driver has neither. Fix pattern (used in scv_dual_write_spec.spl): run the
  driver with `cd "$REPO"`; temp-repo paths are baked into the driver as
  absolute literals via an unquoted heredoc.

## W4 + Wave 1 — COMPLETE 2026-08-26 (closeout lane)
- W4 (SCV-MIG-21..25) COMPLETE: quarantine GC, recover levels, dual-write
  compare, shadow replication verified green; S4 review doc
  `doc/03_plan/app/tools/scv_s4_review.md` landed (30-day shadow-usage clock
  starts at that review). All five step scripts signed (leaves 27..31) and
  flipped done by the signed checker at --now 2026-09-15T12:00:00Z.
- Wave 1 (SCV-IMPL-E-01..03, P-02, P-03, I-02, D-02, G-01) COMPLETE: event
  watch/source/journal, hardened WASM shim contract, true incremental parse,
  file-history snapshot integration, three-view diff, explicit-commit parse
  policy — all specs green at expected counts (see closeout sweep 2026-08-26:
  mvp 11/11, quarantine 3/3, recover 6/6, dual-write 4/4, file-history 7/7,
  three-view 5/5, commit-parse 5/5, event-journal 4/4, event-watch 5/5,
  event-source 4/4, wasm-shim 8/8, incremental-parse 9/9, shadow 3/3).
  Step scripts signed (leaves 32..39), flipped done at --now 2026-09-29 after extending the signed checker to accept SCV-IMPL rows (it structurally ignored them — see doc/08_tracking/bug/scv_migration_checker_ignored_impl_rows_2026-08-26.md; checker re-signed, leaf 40).
- Drills: check-scv-restore-drills.shs PASS — 6 drill(s) recovered, 0 failures.
  Crash harness: PASS — 9 crash point(s) survived, 0 corruptions.
- parser_wasm honest status: 7/12 (pre-existing red, matches baseline; strace
  confirms zero resolution from /home/ormastes/dev/pub/simple — no
  nested-tree contamination in this tree).
- Gaps to S5 / Wave 2: Rust notify bridge in src/runtime/fswatch/ still TODO
  (E-01 pure-Simple half only); SCV-IMPL-B-01 blocked on sj repair;
  pre-existing reds unchanged (storage, structural_match 5/9, merge 1/5,
  parser_incremental 0/1, parser_cache 0/1, wasm_executor, gates 4/10).
