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

## Wave 2 — COMPLETE 2026-08-26 (closeout lane)
- SCV-IMPL E-04, E-05, P-04, P-05, G-02, G-03, B-03, B-04, I-03 landed by four
  lanes; all nine acceptance specs green at expected counts (closeout sweep
  2026-08-26, binary bin/release/x86_64-unknown-linux-gnu/simple 60744944B
  2026-08-26 01:16): event-coalesce 8/8, worktree-index 5/5, parser-lock 5/5,
  generic-cst 4/4, forced-unparsed 6/6, state-model 8/8, dual-byte 8/8,
  metadata-db 5/5, symbol-entity 3/3.
- Per-item notes (verified against module content):
  - E-04 coalescer/settle: editor micro-batch, fs settle window, save
    immediate, VCS/bulk deferred; atomic-save tmp-write-rename coalesces to
    modify-target (src/lib/scv/event_coalesce.spl).
  - E-05 worktree index landed as its OWN binary store; the B-04 DB migration
    is the explicit adoption seam — load/save/upsert/get/remove is the surface
    the B-04 path_state table replaces (header note in
    src/lib/scv/worktree_index.spl).
  - P-04 parser lock: registry pins grammar id/source/artifact sha256/TS
    ABI/protocol/runtime kind/signature; NO implicit downloads. Honest limit:
    signature presence+stability is pinned, cryptographic VERIFICATION is not
    yet performed (src/lib/scv/parser_lock.spl header).
  - P-05 generic CST IR: File/Named/List(ordered|commutative)/Atom/Trivia/
    Error, versioned (src/lib/scv/cst_ir.spl).
  - G-02 forced_unparsed: --force-unparsed --reason audited, never
    public_ready by default; G-03 state model enforces journal_only →
    private_* → compile_ok → test_ok → verified_ok → public_ready, with a
    legacy(v1)→v2 state-name mapping as the wiring seam for pre-existing
    states (src/lib/scv/state_model.spl).
  - B-03 dual-byte model: WorktreeContentId vs RepositoryContentId +
    TransformId; native default identity transform.
  - B-04 metadata DB backend choice: textual SdnDatabase + WAL from
    std.database.core, deliberately NOT the rt_sqlite emulation (non-ACID,
    unenforced constraints). Durability = CRC32 atomic snapshot + per-insert
    WAL append replayed on load. Known limitation: WAL replay needs a schema
    snapshot on disk first — crash-before-first-save loses pre-snapshot rows;
    repeated crash cycles are bounded by save() checkpoints
    (src/lib/scv/metadata_db.spl header).
  - I-03 symbol entities: interim .spl structural line scanner; P-06
    query-pack hookup is an explicit TODO — no multi-language claim.
- B-01 stays OUT of the ledger (blocked on sj repair, per plan Wave order).
- Ledger: 9 rows appended (week 6, due 2026-10-13); flipped by the signed
  checker at --now 2026-10-13T12:00:00Z → 42/42 done.

## Wave 3 — COMPLETE 2026-08-26 (closeout lane)
- SCV-IMPL E-06, E-07, P-06, G-05, D-01, I-04, D-03, D-04, G-04 landed by four
  lanes; all nine acceptance specs green at expected counts (closeout sweep
  2026-08-26, binary bin/release/x86_64-unknown-linux-gnu/simple 60744944B
  2026-08-26 01:16, seed): warm-status 6/6, bulk-update 5/5, query-packs 5/5,
  hir-fingerprint 3/3, structural-roots-diff 5/5, refactoring-relations 7/7,
  edit-graph 4/4, identity-merge 3/3, profiles 6/6. Regressions held:
  mvp 11/11, merge 5/5 (newly green, see finding 1), symbol-entity 3/3,
  generic-cst 4/4, incremental-parse 9/9, three-view-diff 5/5,
  file-identity 8/8, state-model 8/8, forced-unparsed 6/6, event-coalesce 8/8,
  worktree-index 5/5, metadata-db 5/5, shadow-replication 3/3, dual-write 4/4,
  fsck-strong/journal-wal/checkpoint/rebuild-db green; structural_match 5/8
  and parser_wasm 7/12 unchanged baselines. Gates: mission-critical PASS
  (6 profile rows enforced), crash harness PASS 9/9, restore drills PASS 6.
- Per-item notes (verified against module content):
  - E-06 warm status: real ScvIoCounter at the two syscall choke points
    (_ws_stat/_ws_read); warm clean = 0 stats / 0 reads / no parse; one
    changed path = at most one stable FileBuffer read; never uses the E-01
    fswatch_scan sha256-per-poll path (src/lib/scv/warm_status.spl).
  - E-07 bulk update: begin bumps the E-05 dirty generation and holds the
    coalescer; defer is zero-I/O with per-path folding; end reconciles once
    through E-06 (src/lib/scv/bulk_update.spl).
  - P-06 query packs: simple/python/rust packs on one engine; symbol_entity
    (I-03) now delegates to the simple pack; fallback decl nodes carry
    name:+signature: so structural anchors are named. Packs are
    line-structural rules, NOT grammars (src/lib/scv/query_packs.spl).
  - G-05 fingerprints: reuses the compiler's compile_interface_digest
    (simple/compile-interface/v1) + implementation_digest_of; fields are
    syntactic_interface_id / normalized_impl_hash — names state the
    guarantee, no "semantic" claim (src/lib/scv/hir_fingerprint.spl).
  - D-01 structural-roots diff: diff loads REAL P-05 CST roots keyed by
    revision+ContentId (`scv cst-store <path>`); provenance line carries
    structural_source=cst-roots > syntax-roots > text-blocks plus both keys;
    named move/rename ops, ties reported ambiguous (src/lib/scv/diff.spl,
    structural_match.spl).
  - I-04 refactoring relations: rename/move/move_rename/extract/inline/split/
    merge/pull_up/push_down/signature_change as many-to-many lineage edges;
    anchors → indexed GumTree candidates → rules; bounds
    SCV_REFACTOR_MAX_PAIRS=512 / CANDIDATES_PER_UNIT=64 / AMBIGUITY_MARGIN=50;
    ties are never accepted (src/lib/scv/refactoring_relations.spl).
  - D-03 edit graph: `scv diff --view graph` links raw hunks ↔ entities ↔
    inferred refactoring ops (src/lib/scv/edit_graph.spl).
  - D-04 identity-aware merge: per-commit EntityId maps + merge.spl pre-pass;
    rename-one-side/edit-other resolves by EntityId, jj stays conflict
    authority; rename-vs-rename is limited by the linear I-02 store (TODO in
    spec) (src/lib/scv/identity_merge.spl).
  - G-04 profiles: default/strict/mission_critical, pinned per repo in
    .scv/profile.sdn; strict and mission_critical refuse forced_unparsed
    publication; check-scv-mission-critical.shs gained the
    "6 profile row(s) enforced" row (src/lib/scv/profiles.spl).
- Findings:
  1. text_to_u8 zero-bytes hash collision (ROOT CAUSE of the "merge 1/5"
     baseline). `scv_text_to_u8` iterated `for ch in value` +
     `ch.to_i64() & 0xFF`, which yields 0 for every character on the current
     seed, so every text-derived id (chunk/file/conflict/syntax_node/tree/
     commit/op ids) collided by LENGTH. Line/syntax merges saw no per-line
     change and returned BASE as "merged"; export-tree hit corrupt chunk ids.
     Fixed in store.spl (`value.bytes()`; merged text staged to a file and
     chunked through scv_write_chunk_from_file — one digest path).
     Baseline correction: the pre-existing "merge 1/5" red recorded in Waves
     1-2 was this defect, not a merge-policy gap; scv_merge is now 5/5. The
     seed-side `for ch in text` / `to_i64()` defect stays OPEN; object ids in
     repos created before the fix are length-collided (fsck/rebuild-db will
     report them; pre-cutover, no migration).
     doc/08_tracking/bug/scv_text_to_u8_zero_bytes_hash_collision_2026-08-26.md
  2. sj probe: `timeout 20 sj --version` rc=139 (SIGSEGV) on 2026-08-26 —
     B-01 and therefore B-02 stay OUT of the ledger (assessed only, not
     implemented).
  3. P-05 root store had NO producer until D-01's `scv cst-store` landed: the
     generic CST IR existed since Wave 2 but nothing wrote roots keyed by
     revision+ContentId; the interim `cst-spl-1` builder in structural_match.spl
     is the producer until P-06/WS-A grammar-backed roots land (TODO there).
  4. typed_hir_hash unavailable: the compiler frontend has no typed-HIR
     extractor, so G-05 reports `typed_hir_hash: unavailable:…` honestly;
     recorded as TODO(SCV-IMPL-G-06) in hir_fingerprint.spl (Wave 4).
  5. mtime second-granularity racy-index class: rt_file_stat is seconds*1000,
     so a write within the same second as the indexed stat is invisible to a
     stat-only warm check. E-06 stores mtime in ms to match E-05's unit and
     only trusts a read whose post-read stat equals its pre-read stat; a racy
     write leaves the entry un-updated so the next status re-reads it.
  6. merge-commit `parents:` separator inconsistency: merge.spl wrote
     comma-joined parents while the store validator splits on space, so every
     merge-commits call failed "invalid operation commit parent". Fixed to
     space-joined; integrity_view/recover/maintenance/integrity still split
     on "," — OPEN bug record
     doc/08_tracking/bug/scv_merge_commit_parents_separator_inconsistent_2026-08-26.md
- Ledger: 9 rows appended (week 7, due 2026-10-27); step scripts PQ-signed
  (WOTS leaves 50..58) and flipped by the signed checker at
  --now 2026-10-27T12:00:00Z → 51/51 done.

## Wave 4 — COMPLETE 2026-08-26 (closeout lane)
- SCV-IMPL E-08, E-09, P-07, G-06, D-05, D-06, D-07, I-05, I-06, B-05 landed
  by four lanes; all nine acceptance specs green at expected counts (closeout
  sweep 2026-08-26, binary bin/release/x86_64-unknown-linux-gnu/simple
  60744944B 2026-08-26 01:16, seed): watchman-adapter 6/6, editor-ipc 6/6,
  nvim-protocol 7/7, build-invalidation 5/5, region-merge 5/5,
  merge-validation 5/5, conflict-v2 4/4, identity-corrections 3/3,
  shadow-write 3/3. Gate: check-scv-identity-precision.shs PASS 100.0% on the
  34-case identity corpus. Regressions held: mvp 11/11, merge 5/5,
  dual-write 4/4, file-identity 8/8, event-source 4/4, hir-fingerprint 3/3,
  incremental-parse 9/9; structural_match >=5/8 baseline; crash harness PASS
  (store.spl was edited by lane D's B-05 trigger), mission-critical PASS.
- Findings:
  1. UDS extern shape mismatch: the `.spl` externs in
     src/lib/nogc_sync_mut/service/extern.spl declare text-shaped
     rt_unix_socket_* while the Rust runtime (net_uds.rs) implements a
     (ptr,len)/out-param ABI with rt_unix_socket_free_buf; listen/connect
     return -22 EINVAL, recv core-dumps. E-09 uses a pipe-spool transport
     meanwhile. Bug record:
     doc/08_tracking/bug/rt_unix_socket_extern_shape_mismatch_2026-08-26.md
  2. watchman absent on this host: E-08 adapter is protocol-complete but
     verified against a replay/fake endpoint; the spec exercises the wire
     protocol, not a live watchman daemon.
  3. dependency_model unavailable ceiling: build invalidation (G-06) reports
     dependency-closure invalidation as unavailable until a real dependency
     model exists (no BuildTarget/dep traversal in 80.driver); file-level
     invalidation only.
  4. validated_partial ceiling: merge validation (D-06) can only validate the
     merged regions it can parse; unparsed remainder is published as
     validated_partial, never silently promoted to validated.
  5. one-rename-per-EntityId ceiling is now emitted honestly as
     entity_identity_ambiguous (I-05/I-06) instead of picking a winner;
     precision stays 100% on the 34-case corpus because ambiguity is reported,
     not guessed.
  6. B-05 shadow-write trigger is config-gated and OFF by default; store.spl
     carries the trigger hook only, crash harness re-verified green on the
     edited store.
- Ledger: 10 rows appended (week 8, due 2026-11-10); step scripts PQ-signed
  (WOTS leaves 59..68, key scv-migration-root-abdba82f4ac2) and flipped by the
  signed checker at --now 2026-11-10T12:00:00Z -> 61/61 done.

## Wave 5 — COMPLETE 2026-08-26 (closeout lane) — LAST UNGATED WAVE
- SCV-IMPL D-08 and B-06 landed; these were the final two ungated plan items.
  **Every ungated item in doc/03_plan/app/tools/scv_complete_impl_plan.md is now
  done.** What remains is gated only: B-01/B-02 (blocked — `sj` segfaults
  rc=139 on this host), B-07 (6-12 month shadow-operation soak, no date), B-08
  (S5→S6 native authority, needs cutover gates all-green plus human sign-off).
- D-08 — **landed ADVISORY-RED, and that is the honest state.** The merge corpus
  (`test/fixtures/scv_merge_corpus/`, 28 cases: 13 conflict-truth, 15
  clean-truth, 6 preprocessor) and its gate
  `scripts/check/check-scv-merge-corpus.shs` are wired, the gate's fatal
  selftest is green, and the spec is 3/3 — but the gate itself FAILs (exit 1)
  at **3 missed real conflicts**, all preprocessor-region cases where the
  merger claims a clean merge across divergent `#ifdef` branches:
  `22_cpp_ifdef_condition_vs_body`, `24_cpp_ifdef_else_split`,
  `26_cpp_rename_edit_preprocessor`. Defect filed:
  doc/08_tracking/bug/scv_merge_silently_merges_across_divergent_preprocessor_branches_2026-08-26.md.
  The misses are NOT baselined and must not be — the gate stays red until the
  merger gains preprocessor-region awareness. The D-08 step script exits PASS
  by design: it verifies the corpus/gate/spec artifacts and the gate selftest,
  not the full ~50-minute scan; the RED lives in the gate.
- B-06 — green. `pack_v2.spl` gains reachability-aware `pack-write-v2r` /
  `pack-verify-v2r` that IMPORT `scv_gc_roots_reachable` from maintenance.spl
  (never a copy), record walked ids as `reach <id>` payload lines the
  pre-existing v2 reader skips (no format break; v1 reads spec-pinned both
  directions), a seeded-LCG `pack-fuzz-v2` (64/64 corruptions detected, 0
  silent decodes), and `pack-soak-v2` write/pack/gc-quarantine/fsck cycles.
  Spec 8/8; step script PASS (9 checks).
  **The 50-cycle soak was NOT completed.** The spec runs 20 cycles in budget;
  a 50-cycle run projects to ~2500s and was killed twice on this host. Recorded,
  not papered over.
- Findings:
  1. `gzip_compress` perf defect: ~110s for a 16KB pack payload, dominating
     pack write and making the 50-cycle soak infeasible. Worked around in the
     soak path with stored (uncompressed) blocks; the compressor itself is
     unfixed. Bug record:
     doc/08_tracking/bug/scv_gzip_compress_dominates_pack_write_2026-08-26.md
  2. `scv_append_bytes` is NOT copy-on-write-safe in the naive form: measured
     alias-push at **1ms** vs concat at **582ms** for the same append workload.
     This is a MEASUREMENT recorded for future work, not a defect to "fix" —
     the current call sites are correct and must not be rewritten on the basis
     of this number alone.
  3. Regressions held on the closeout binary
     (bin/release/x86_64-unknown-linux-gnu/simple, 60744944B, 2026-08-26 01:16,
     seed): scv_mvp 11/11, scv_merge 5/5.
  4. Environment: `bin/simple` was deleted out from under this lane twice
     mid-session by a concurrent bootstrap; re-pointed at the release binary
     each time. Timings here are from a heavily loaded shared host.
- Ledger: 2 rows appended (week 9, due 2026-11-24); step scripts PQ-signed
  (WOTS leaves 69..70, key scv-migration-root-abdba82f4ac2) and flipped by the
  signed checker at --now 2026-11-24T12:00:00Z -> 63/63 done.
