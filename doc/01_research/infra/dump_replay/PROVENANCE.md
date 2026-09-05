# Provenance — dump/replay/firmware design set, 2026-09-05

Imported 2026-09-05 from `~/Downloads`, delivered as a four-artifact set.

## Files and verification

The three content files are stored **byte-verbatim**, with no import header
added, so `shasum -a 256` still reproduces the delivered digest. (The
2026-09-04 import at `../spipe/spipe_skill_foundry_debug_training.md` did carry
a prepended header, which means its checksum no longer verifies in place —
verify that one against `~/Downloads` or git history instead.)

| file | sha256 | verified |
|---|---|---|
| `simple_dump_replay_fw_spipe_devhub_design_plan_2026-09-05.md` | `112237e4…8cd9a3` | yes, twice (pre- and post-copy) |
| `simple_dump_replay_fw_spipe_devhub_validation_2026-09-05.md` | `fa9acf54…afeb7d07` | yes |
| `../spipe/spipe_skill_foundry_debug_dump_replay_v2_2026-09-05.md` | `e85c52e5…c24eb383` | yes |

`spipe_skill_foundry_debug_dump_replay_checksums_2026-09-05.txt` is the
as-delivered manifest, stored unmodified. Its first line re-attests the
2026-09-04 design plan at `2d99dc7d…b1690411`, the same digest recorded for
`../spipe/spipe_skill_foundry_debug_training.md` — so that earlier import is
independently confirmed by this later manifest.

## What is different from the 2026-09-04 delivery

**Every artifact the manifest names was actually delivered.** The 09-04 set
listed a companion `spipe_skill_foundry_debug_training_platform_2026-09-04.zip`
that was never downloaded, which made that day's `VALIDATION_REPORT.md`
green results unattributable to anything present. This set names four files and
ships four files; there is no zip and no unvalidated companion.

`simple_dump_replay_fw_spipe_devhub_validation_2026-09-05.md` is also scoped
honestly: it reports structural validation (line/word/byte counts, fence
balance, required-section presence) and states its repository audit boundary as
GitHub default-branch head `320e6d99e4b8b8540a65078f68ce8ffca15fd2b6` —
the exact origin tip PR #371 was rebased onto — while explicitly recording that
no repository file was created or modified. It does **not** claim any behaviour
was executed. Read it as a document-integrity report, not as evidence that the
design works.

## Relationship to the 2026-09-04 foundry plan

`../spipe/spipe_skill_foundry_debug_dump_replay_v2_2026-09-05.md` is a
consolidated v2 (3,800 lines) of
`../spipe/spipe_skill_foundry_debug_training.md` (1,752 lines). The v1 file is
retained rather than overwritten: it is the artifact the 09-04 checksum
manifest attests, and the flywheel audit recorded against it
(`doc/00_llm_process/feature_expert/modern_sspec/skill.md`) cites its content.
Prefer v2 for new work; treat v1 as the dated original.

`simple_dump_replay_fw_spipe_devhub_design_plan_2026-09-05.md` is the focused
addendum (2,071 lines) covering state capsules, deterministic replay, T32,
SimpleEMU, and CPU/GPU profiling.

## Bearing on the open dump/load work

The design's central decision — one normalized `StateCapsuleV1` contract
extending the already-designed `DebugServiceV1` and `DebugEvidenceBundleV1`,
rather than a third debugger or second evidence vault — is consistent with what
is already landed at
`doc/07_guide/app/debug/debug_evidence_bundle_contract.md`.

Two claims in it must not be read as repo status:
- It describes `DebugServiceV1` and `DebugEvidenceBundleV1` as "existing
  architecture to extend". The bundle *reader* exists
  (`src/app/cli_debug/evidence_inspect_v1.spl`) and its rejection paths are
  covered by a passing conformance spec, but **nothing in the repo writes a
  bundle** — no `.spl` emits a `manifest.sdn`.
- The reader is additionally blocked: `evidence_inspect_v1.spl:159` reads
  `outcome.receipt_id`, a field `DebugReceiptV1`
  (`src/lib/common/debug/contracts_v1.spl:59-67`) does not have. Filed as
  `doc/08_tracking/bug/debug_evidence_inspect_receipt_id_field_missing_2026-09-05.md`.

The plan's own claim controls (strict-zero reserved for compile-time omission
proven at final-artifact level; core/fault dump analysis-only unless complete
restore state is demonstrated; reverse execution requiring checkpoint restore
plus deterministic replay) are the right bar and should be held to when the
writer is built.
