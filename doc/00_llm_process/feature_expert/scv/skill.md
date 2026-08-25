# Feature Expert: SCV (Simple Code Versioning)

## Role

Own feature-specific process knowledge for SCV: the content-addressed,
parser-aware version-control tool (`src/lib/scv/`, CLI `src/app/scv/main.spl`).

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Feature Links

- Research: `doc/01_research/app/tools/scv/scv_v2_final_report_2026-08-25.md`,
  `doc/01_research/app/tools/scv/scv_migration_stabilization_2026-08-25.md`
- Design: `doc/05_design/app/tools/scv.md` (incl. "Stabilization Commands" §)
- Source: `src/lib/scv/` (store, working_copy, integrity*, stabilize, parser*,
  pack*, merge, refs, fast_import, remotes), `src/app/scv/main.spl`
- Specs: `test/integration/app/scv_*_spec.spl`

## Current State (2026-08-25, P0 foundation landed)

- Persistent logical ChangeId: snapshot path carries the open change id across
  re-snapshots (`scv_write_commit_carry`, store.spl); allocation is
  counter+time based (`meta/change_seq.sdn`), never content-derived from the
  mutable latest revision. Change objects are `format: 2` with
  `state: open|closed`; v1 objects still read (as open) and upgrade on write.
  CLI: `new-change`, `close-change`. Fast-import/merge keep deterministic
  derived ids on purpose (idempotent re-import).
- Stabilization tooling in `src/lib/scv/stabilize.spl`: `checkpoint`
  (+`verify`, `list`), `doctor` (OK|STALE|FAIL rows, fail-closed verdict,
  reconciles the derived workspace pointer from the published head view),
  `verify-backends --git <path> [--rev r]` (byte-exact via `git hash-object`).
- Write-new-then-publish protocol with `SCV_FAULT_AFTER` fault hook
  (`scv_fault_exit`, store.spl); HEAD_OP is the single publication point.

## Constraints / Known Blockers

- `bin/simple` is the Rust seed; specs shell out via
  `SIMPLE_LIB=$REPO/src bin/simple run src/app/scv/main.spl ...`.
- Pre-existing red (NOT this feature): `fsck` on a fresh repo reports
  `bad parser lock entry` — init writes a legacy 3-line parser lock while
  `scv_validate_parser_lockfile` expects 8-field `parser|...` rows. New specs
  therefore filter fsck output for structural errors instead of asserting a
  blanket OK.
- Run scv specs ONE AT A TIME (`bin/simple test <spec>`); only the
  `Results: N total, ...` line is an authoritative verdict.

## Verification Commands

```bash
bin/simple test test/integration/app/scv_changeid_spec.spl
bin/simple test test/integration/app/scv_checkpoint_spec.spl
bin/simple test test/integration/app/scv_doctor_spec.spl
bin/simple test test/integration/app/scv_verify_backends_spec.spl
bin/simple test test/integration/app/scv_fault_injection_spec.spl
```

## Update Rule

When SCV research/design/impl/spec artifacts change, update this skill's links
and handoff notes in the same change.
