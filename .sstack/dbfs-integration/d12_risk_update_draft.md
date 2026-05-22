# D12 Risk Register — Proposed Update (DRAFT)

**Feature:** dbfs-integration
**Phase:** 6-refactor (parallel D12 update track)
**Date:** 2026-04-28
**Status:** DRAFT — for user review; not yet applied to `doc/04_architecture/dbfs_architecture.md`
**Source-of-truth read (verbatim baseline):** `doc/04_architecture/dbfs_architecture.md` §D12 (lines 458–474, 13 rows)
**Inputs consumed:** `risk_premortem.md`, `hw_passthrough_audit.md`, `verify_plan.md`, `state.md`
**Locked-doc rule:** D1–D12 are immutable. This draft is a proposed *additive*
change. The user MUST decide whether to amend §D12 in-place, attach this as a
D12-Appendix, or carry forward into a new D14 (Process Risks) section.

---

## Proposed change

Adds **R14, R15, R16, R17**. **No existing rows changed** except a severity
re-statement note for **R7** (the prompt requested R7 remain HIGH, but the
locked doc records R7 as MEDIUM — see §3 below for the discrepancy callout;
the user must adjudicate).

The prompt also asked for "R3 downgraded MED-HIGH → MED post-DURABLE_GROUP_COMMIT".
The locked doc already lists R3 as MEDIUM, so no row change is needed; the
downgrade has already been applied at architecture-lock time. Recorded here
as a *no-op confirmation*, not a wording change.

The prompt also asked R1, R2, R7 to remain HIGH. R1 and R2 already are HIGH;
R7 is currently MEDIUM in the locked doc. Since this draft is forbidden from
silently rewriting R1–R13, R7's severity is **flagged but not edited** — the
user can promote R7 to HIGH if they agree with the pre-mortem stance.

---

## §1. Existing 13 D12 risks — verbatim baseline

(Copied verbatim from `doc/04_architecture/dbfs_architecture.md` §D12,
lines 460–474. Diff target: this block must be byte-identical to upstream
when the user reads the architecture doc, otherwise the draft is stale.)

| # | Risk | Severity | Mitigation |
|---|------|----------|------------|
| R1 | Intent log persistence gap (HIGH) | HIGH | Gap 4 is a required deliverable; must flush to DB_WAL arena before returning from wal_append; spec in wal_spec.spl verifies durable return |
| R2 | Checkpoint ring persistence gap (HIGH) | HIGH | Gap 5 is a required deliverable; CheckpointEntry written to META_DURABLE before clean=true; spec in recovery_spec.spl verifies post-crash ring scan |
| R3 | Double journaling (DBFS WAL + NVMe FTL) | MEDIUM | Use DURABLE_GROUP_COMMIT (one flush per commit, not per record); document explicitly in AC-10 doc; no per-record fsync |
| R4 | Double cache (DBFS buffer manager + kernel page cache) | MEDIUM | Single-cache discipline: DBFS pages keyed by (ino_id, page_id); kernel cache keyed by (device_id, lba); never cross-insert; verified in Phase 7 |
| R5 | Large-file random overwrite COW amplification | MEDIUM | Random write rewrites one EXTENT_REF per 4K write (worst case); mitigated by extent coalescing in vacuum pass; benchmarked in random_overwrite_bench.spl |
| R6 | Namespace B-tree key generalization mismatch | MEDIUM | pmap_btree structural copy with DentryKey; btree_spec.spl ports all 3 original tests to new key type; no runtime behavior change |
| R7 | Power-cut harness complexity (AC-5) | MEDIUM | Harness wraps Arena with fault injection (N-write threshold); simpler than real device testing; interpreter-mode only |
| R8 | simple_db_if Rel/BlkNo coupling leak | MEDIUM | DbFsEngine defines own Ino/DirEntryKey; never imports Simple DB type definitions; enforced by no cross-module import of Simple DB types |
| R9 | Recovery bugs in orphan reclamation | MEDIUM | arena_discard is idempotent; worst case: disk space not reclaimed, not data corruption; recovery_spec verifies no false-positive discards |
| R10 | jj submodule gitlink flip during parallel work | LOW | Per memory note: accept gitlinks-as-tree; commit per-phase immediately; no parallel /dev tracks during DBFS phase work |
| R11 | Stage 2 rt_* extern bootstrap rebuild | LOW | Any new rt_* extern requires full bootstrap (scripts/bootstrap/bootstrap-from-scratch.sh --deploy); documented in implementation handoff |
| R12 | Scope creep (distributed NVFS, xfstests, mmap shared-write) | LOW | Explicitly out of scope per Phase 1 decisions; out-of-scope list locked in D10 |
| R13 | Submodule race with parallel /dev auto-snapshot | LOW | Per memory `feedback_submodule_race_parallel_dev`: jj auto-snapshot between stage and commit converts gitlinks to 040000 tree. Mitigation: pause all parallel sstack/dev tracks before starting DBFS phase work; resume only after each atomic commit lands. Commit per-phase immediately (per `feedback_sync_bundling_clobbers_commits`). |

**End verbatim block.** Anything below this point is a proposed addition.

---

## §2. Proposed new risks (R14–R17)

Format matches §D12 columns (`# | Risk | Severity | Mitigation`) plus extended
columns for *Failure scenario*, *Why mitigation might fail*, *Counter-mitigation*,
*Earliest detectable signal*, *Source*, and *Routing* (Phase 6 / 7 / 8).

### R14 — Compile-mode false-greens

| Field | Value |
|---|---|
| Severity | **MEDIUM-HIGH** (cover-up vector — passes that aren't proofs) |
| Source | `risk_premortem.md` §R11; memory `feedback_compile_mode_false_greens` (2026-04-25) |
| Failure scenario | Ship-day + 12 days. Downstream user runs DBFS benchmarks under `--mode=native` per their CI default. `feedback_compile_mode_false_greens` documents that `--mode=native` stub-generates unresolved `std.spec` calls into no-ops, and `--mode=smf` swallows runtime errors. Both modes still report `PASSED`. The user's "passing" benchmark is running zero work; reported IOPS ~10× the real number. |
| Why arch D11 doesn't catch it | D11 says "all specs are interpreter-mode only" — this is a *constraint statement*, not an enforced ship-gate or runtime guard. No spec asserts its own mode. No CI lane refuses a `--mode=native` invocation. AC-10 documentation does not ban native/smf for DBFS specs. |
| Mitigation | Spec-header guard line `# verified-mode: interpreter` parsed by the test runner; runner refuses `PASS` for any DBFS spec invoked under `--mode=native` or `--mode=smf`. |
| Counter-mitigation | (a) Add `assert_interpreter_mode_or_skip()` at the top of every `test/dbfs/*_spec.spl`. (b) Add Phase 8 ship-gate script that confirms at least one CI lane runs `bin/simple test` with no `--mode=` flag. (c) CI reject if `--mode=native` ever runs against `test/dbfs/`. (d) Document the constraint in `dbfs_architecture.md` §D11 and in spec file headers. |
| Earliest detectable signal | A DBFS spec runs and prints `[mode=native]` or `[mode=smf]` instead of `[mode=interpreter]` in its banner line. |
| Routing | **Phase 6** — add the spec-header guard during refactor (cheap, additive). **Phase 7** — verification plan §0 already pins interpreter mode (per `verify_plan.md`); Phase 7 must execute the negative test (run a DBFS spec under `--mode=native` and confirm the runner refuses to record PASS). **Phase 8** — ship-gate script lands. |

---

### R15 — jj uncommitted-edit clobber by parallel /dev

| Field | Value |
|---|---|
| Severity | **MEDIUM** (operational; correctness-adjacent, not correctness itself) |
| Source | `risk_premortem.md` §R12; memory `feedback_jj_uncommitted_clobbered_by_parallel` (2026-04-27) |
| Failure scenario | Ship-day − 4 hours. Phase 5 agent has Edit-tool changes staged in 3 `.spl` files but not yet jj-snapshotted. A second parallel /dev track fires `jj commit` for an unrelated feature. jj reconciles the working copy and silently removes the un-snapshotted Edit-tool changes. The Phase 5 agent re-runs tests, sees them pass *because the broken edits were the missing fix that's now gone*, and ships. Production builds fail; the missing edits were a fix for an exit-code bug introduced earlier in the session. |
| Why R10/R13 don't cover it | R10 covers `jj` *submodule gitlink* flips (160000 → 040000 for git-managed inner repos). R13 covers parallel-/dev *submodule race during stage→commit*. Neither covers plain working-copy `Edit`-tool edits being silently dropped during reconcile. R15 is a strictly distinct mechanism. |
| Mitigation | Per-edit auto-`jj commit` after each lint-clean sub-batch, before any further tool calls. Documented as a process invariant in `CONTRIBUTING.md` and `.claude/rules/vcs.md`. |
| Counter-mitigation | (a) Add to `dbfs_architecture.md` Module Map Summary or a new "Phase 5 Process Invariants" section: "After each `*_spec.spl` or engine-source edit, immediately `jj commit -m \"wip(dbfs): <file>\"` before issuing further tool calls." (b) Pre-flight check in DBFS sub-agent prompts: "If you have un-jj-snapshotted edits and no exclusive lock on the working copy, commit before yielding." (c) Phase 7 pre-amble must `jj diff` baseline before running anything else. |
| Earliest detectable signal | `jj diff @` shows fewer changed files than the agent's edit log claims. Or: `git diff` against the last known good ref shows a missing hunk that the agent's transcript records writing. |
| Routing | **Phase 6** — document the invariant in `vcs.md` / CONTRIBUTING (already covered partly by `.claude/rules/vcs.md`). **Phase 7** — confirm during verification preamble that no parallel /dev track was active during Phase 5 (per `verify_plan.md` §6 R13 evidence path, which already does this for gitlink flips — extend the same check to working-copy diff stability). **Phase 8** — no ship-impact (process discipline, not code). |

---

### R16 — BlobBackend conformance gap (RawNvmeArena not on disk at lock time)

| Field | Value |
|---|---|
| Severity | **MEDIUM** (architecture commits a contract the code does not yet satisfy) |
| Source | `risk_premortem.md` §R13; cross-checked against `state.md > Phase Outputs > 6-refactor > Track B`; D6 BlobBackend decision in `state.md > 3-arch > D6` |
| Failure scenario | Architecture D6 collapses BlobBackend to the existing `Arena` trait with two impl claims: NVFS Arena (real, on-disk in `src/lib/nogc_sync_mut/storage/arena.spl`) and `RawNvmeArena` (the raw-NVMe path required for AC-6 hardware passthrough). Phase 5 closed without `RawNvmeArena.spl` being on disk — the conformance suite, the only proof that *both* impls satisfy the contract, was therefore single-impl. A future refactor could break the unwritten impl invisibly because no second-impl test exists to flush the assumption out. |
| Why D6 alone doesn't catch it | D6 names the trait and its semantics but doesn't enforce that ≥2 impls exercise the conformance suite. Single-impl trait conformance is indistinguishable from "the trait *is* the impl" — a degenerate proof. |
| Mitigation | A shared conformance suite (`test/dbfs/arena_conformance_suite.spl`) parameterized over backend, invoked by every backend-spec. |
| Counter-mitigation | Phase 6 Track B closes this by (a) adding `src/lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena.spl` (~250 LoC implementing `Arena` over `BlockDevice`, per Phase 3 D2), and (b) tightening `test/dbfs/dbfs_hw_passthrough_spec.spl` to assert wire-through (not just driver-name text). |
| Earliest detectable signal | `grep -RnE 'impl Arena' src/lib/nogc_sync_mut/` returns < 2 hits, while D6 claims ≥ 2 impls. Currently exactly this case as of Phase 5 close. |
| Routing | **Phase 6** — addressed by Track B items 5 (RawNvmeArena) and 7 (passthrough spec tightening), per `state.md > 6-refactor`. **Phase 7** — verifies via `bin/simple test test/dbfs/raw_nvme_backend_spec.spl` (planned in Phase 7 verification matrix AC-4) and via the static check `grep -c 'impl Arena' src/lib/nogc_sync_mut/ ≥ 2`. **Phase 8** — no ship-gate work; closure is upstream of ship. |

---

### R17 — `mount_table` write/pread/pwrite/close hard-codes `self.mounts[0]`

| Field | Value |
|---|---|
| Severity | **MEDIUM-HIGH** (real AC-2 regression bug; cover-up-by-luck if only one mount is ever active) |
| Source | `hw_passthrough_audit.md` §6 R6 (located at `mount_table.spl:209+`); cross-listed in `state.md > 6-refactor > Track B` item 6 |
| Failure scenario | A user mounts FAT32 at `/boot` and DBFS at `/data`. They open a file under `/data/x` (resolves correctly via `MountTable.resolve` longest-prefix), then issue `write(fd, ...)`. `MountTable.write` skips its own resolver and dispatches to `self.mounts[0]` — the FAT32 driver. The write either errors (best case) or — if the fd handle happens to be reusable across drivers — silently writes DBFS payload bytes through the FAT32 path, corrupting the FAT32 volume. AC-2 (DBFS lands at FsDriver seam without breaking other mounts) regresses. The bug is masked any time only one mount is configured (AC-7 single-mount FAT32 boot path) — including the existing `dbfs_hw_passthrough_spec` if it tests with a single mount. |
| Why existing audit doesn't catch it | Audit §6 R6 marks this *low (but real)* because in current trees only one mount is exercised in testing. The bug is dormant, not absent. The instant a second mount is added (AC-2's whole premise), corruption is one syscall away. The "low" rating in the audit is a snapshot rating; severity rises to MEDIUM-HIGH the moment the second mount lands. |
| Mitigation | All four routing methods (`write`, `pread`, `pwrite`, `close`) must resolve the target mount via the *same* longest-prefix-match path the open/read methods use — never `self.mounts[0]`. |
| Counter-mitigation | (a) Phase 6 Track B item 6 fixes `mount_table.spl:209+` by routing every method through a private `_dispatch(fd_or_path) -> Mount&` helper. (b) Tighten `mount_table_dbfs_dispatch_spec.spl` so the FAT32-and-DBFS-both-mounted scenario writes through DBFS and asserts the byte landed in the DBFS arena, not in any FAT32 sector. (c) Phase 7 must re-run `mount_table_dbfs_dispatch_spec.spl` with both mounts configured and a write to the *non-zeroth* mount; assert correct routing. |
| Earliest detectable signal | (a) `grep -nE 'self\.mounts\[0\]' src/lib/nogc_sync_mut/db/dbfs_driver/mount_table.spl` returns ≥ 1 hit. (b) Spec `mount_table_dbfs_dispatch_spec.spl` written with both FAT32 and DBFS mounts, executing a write to `/data/x`, observes the byte on the FAT32 backend. |
| Routing | **Phase 6** — Track B item 6 fixes; Track B item 7 tightens the spec. **Phase 7** — re-runs `mount_table_dbfs_dispatch_spec` with multi-mount configuration; required as new evidence row for D12-R17 in `verify_plan.md > 6. Risk-to-Evidence Map`. **Phase 8** — ship-gate must confirm `grep self.mounts[0]` returns 0 in `mount_table.spl`. |

---

## §3. Severity reordering — discrepancies and proposed re-statement

Per the user prompt, the requested severity tiering is:

* **HIGH**: R1, R2, R7
* **MEDIUM-HIGH**: R14, R17 (cover-up vectors)
* **MEDIUM**: R3 (post-DURABLE_GROUP_COMMIT), R4–R9 except R7
* **LOW**: R10–R13

Compared to the locked doc:

| # | Locked-doc severity | Prompt-requested severity | Action |
|---|---|---|---|
| R1 | HIGH | HIGH | no change |
| R2 | HIGH | HIGH | no change |
| R3 | MEDIUM | MEDIUM | no change (already applied — confirm only) |
| R4 | MEDIUM | MEDIUM | no change |
| R5 | MEDIUM | MEDIUM | no change |
| R6 | MEDIUM | MEDIUM | no change |
| **R7** | **MEDIUM** | **HIGH** | **DISCREPANCY — user must decide; this draft does NOT silently rewrite R7** |
| R8 | MEDIUM | MEDIUM | no change |
| R9 | MEDIUM | MEDIUM | no change |
| R10 | LOW | LOW | no change |
| R11 | LOW | LOW | no change |
| R12 | LOW | LOW | no change |
| R13 | LOW | LOW | no change |
| R14 (NEW) | — | MEDIUM-HIGH | proposed |
| R15 (NEW) | — | MEDIUM | proposed |
| R16 (NEW) | — | MEDIUM | proposed |
| R17 (NEW) | — | MEDIUM-HIGH | proposed |

**R7 promotion rationale (if user accepts):** `risk_premortem.md` §R7 frames
recovery-bug ambiguity (committed-vs-uncommitted) as a HIGH-severity scenario
because it directly causes silent data loss, not merely "harness complexity."
The locked doc R7 row, however, is scoped to *harness* complexity (AC-5
power-cut testing), which is genuinely a MEDIUM concern. These are arguably
*different* risks sharing a number; the user may prefer (a) leave R7 at MEDIUM
and add a new R18 "Recovery commit-boundary ambiguity (HIGH)", or (b) promote
R7 and rewrite its row to encompass the broader scenario. **This draft does
neither — flagged for adjudication.**

---

## §4. Routing breakdown summary

| Risk | Phase 6 work | Phase 7 verification | Phase 8 ship-gate |
|---|---|---|---|
| R14 compile-mode false-greens | spec-header guard, runner reject hook | run negative test (`--mode=native` must NOT record PASS) | confirm CI lane uses no `--mode=` flag |
| R15 jj uncommitted clobber | document invariant in vcs.md | preamble `jj diff` stability check | n/a (process, not code) |
| R16 BlobBackend conformance | add `RawNvmeArena.spl`, tighten `dbfs_hw_passthrough_spec` | run `raw_nvme_backend_spec`, assert ≥2 `impl Arena` | n/a (closure upstream) |
| R17 mount_table[0] hard-code | fix `mount_table.spl:209+`, tighten dispatch spec | re-run `mount_table_dbfs_dispatch_spec` with two mounts | grep-check `self.mounts[0]` == 0 hits |

**Routing tally:** 4 risks, 4 Phase-6 closures, 4 Phase-7 verifications, 2 Phase-8 ship-gate items.

---

## §5. Diff-friendly application instructions (for the user)

To apply this draft to the architecture doc:

1. **Option A — In-place §D12 extension.** Append rows R14–R17 to the §D12
   table in `doc/04_architecture/dbfs_architecture.md` (lines 462–474 today).
   Keep R1–R13 wording byte-identical. The §D12 row count grows from 13 → 17.
   The `verify_plan.md > 6. Risk-to-Evidence Map` "risk-count sanity" check
   (`grep -c '^| R[0-9]' doc/04_architecture/dbfs_architecture.md must equal 13`)
   must be updated to expect 17 — this is a coordinated edit.

2. **Option B — D12-Appendix block.** Insert the §2 content above as a new
   subsection "§D12.A Process & Operational Risks (R14–R17)" immediately after
   §D12. Keeps the original 13-row table untouched (preserves the count guard)
   and isolates pre-mortem additions for traceability. Recommended if the
   "D1–D12 are immutable" rule is interpreted strictly.

3. **Option C — Defer to D14.** Open a new §D14 "Process Risks" section
   alongside the technical D12. R14 and R15 fit there cleanly (process); R16
   and R17 are technical and probably want to live in D12 proper. This splits
   the draft across two destinations.

The draft author recommends **Option B** — minimum disruption to the locked
doc, full traceability, and the `verify_plan.md` count guard stays valid as-is.

---

## §6. Open questions for the user / orchestrator

1. **R7 severity** — accept locked-doc MEDIUM, or promote to HIGH (and possibly
   reword to encompass the recovery-ambiguity scenario from `risk_premortem.md` §R7)?
2. **Apply mode** — Option A, B, or C in §5?
3. **Should `verify_plan.md > 6. Risk-to-Evidence Map`** be regenerated to add
   evidence rows for R14–R17? (Recommended: yes; orchestrator should route to
   the verify-plan agent in Phase 6 close.)
4. **Are R14 and R15 truly D12 material**, or do they belong in a new
   `CONTRIBUTING.md` / `.claude/rules/vcs.md` extension as *process discipline*?
   (Author opinion: list them in D12 because the architecture doc is the
   ship-gate canonical reference; process invariants enforced by D12 get the
   most reach.)

---

## §7. Advisor verdict (rate-limited; partial)

The advisor was rate-limited at draft time. Author self-review on the merge
question:

* **R14 vs existing R7 ("interpreter-mode only" mention)** — distinct.
  R7's "interpreter-mode only" is a *property of the power-cut harness*,
  not a *ship-time invariant* across all DBFS specs. Different scope; do not merge.
* **R15 vs existing R10 (gitlink flip) and R13 (parallel-/dev submodule race)** —
  distinct mechanism. R10/R13 are about submodule gitlinks; R15 is about plain
  working-copy file edits. Separate memory feedback notes confirm. Do not merge.
* **R16 vs existing R8 (Simple DB coupling)** — different. R8 is about *type*
  coupling at the import boundary; R16 is about *trait conformance proof
  density* (how many impls exercise the conformance suite). Do not merge.
* **R17 vs existing R6 (B-tree key generalization)** — different. R6 is a
  *port-time* concern; R17 is a *runtime dispatch bug* in mount-table routing.
  Do not merge. **R17 should be applied even if the user defers the others** —
  it is a real, located, actionable bug per `hw_passthrough_audit.md` §6 R6
  and `state.md > 6-refactor > Track B` item 6.

A second advisor pass once rate-limit clears is recommended specifically for
the R7 promotion question, which is the only judgement-call ambiguity left.

*End of draft.*
