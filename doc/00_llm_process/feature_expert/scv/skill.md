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

## Post-W4 / Wave-1 status (2026-08-26)
Week 4 (SCV-MIG-21..25) and Wave 1 (SCV-IMPL-E-01..03, P-02, P-03, I-02,
D-02, G-01) are landed and green. New capabilities: conservative quarantine
GC (`src/lib/scv/gc.spl`), leveled recovery (`stabilize.spl`), dual-write
independent compare + shadow replication, S4 review
(`doc/03_plan/app/tools/scv_s4_review.md`, 30-day shadow clock started),
file-system event watch/source (`src/lib/nogc_async_mut/file_system/`),
event journal on the W2 WAL, hardened WASM shim contract
(`src/runtime/scv_wasm_shim.c` + `test/integration/runtime/scv_wasm_shim_contract_spec.spl`),
true incremental parse (persistent ParserSession), file-history CLI
(`scv file-history`, `src/lib/scv/file_history.spl`), three-view diff, and
explicit-commit parse policy. All 13 step scripts PQ-signed (WOTS leaves
27..39; checker re-signed at leaf 40 after being extended to accept SCV-IMPL rows, see doc/08_tracking/bug/scv_migration_checker_ignored_impl_rows_2026-08-26.md); ledger `.spipe/scv-migration/todo.sdn` shows MIG-01..25 + 8 Wave-1
rows done. Known gaps: Rust notify bridge (src/runtime/fswatch/) TODO;
SCV-IMPL-B-01 blocked on sj repair; pre-existing reds unchanged
(parser_wasm 7/12, structural_match 5/9, merge 1/5, gates 4/10, storage,
parser_incremental, parser_cache, wasm_executor).

## Post-Wave-2 (2026-08-26)
Wave 2 (SCV-IMPL E-04, E-05, P-04, P-05, G-02, G-03, B-03, B-04, I-03) is
landed and green (closeout sweep 2026-08-26; regressions all held, incl.
mvp 11/11, file-identity 8/8, incremental-parse 9/9, wasm-shim 8/8). New
capabilities: event coalescer/settle layer (`src/lib/scv/event_coalesce.spl`);
persistent binary worktree index (`worktree_index.spl` — own store; B-04 DB
migration is the documented adoption seam); parser trust/lock v2 registry
(`parser_lock.spl` — pins sha256/ABI/protocol/signature, no implicit
downloads; signature is pinned, NOT cryptographically verified yet); generic
CST IR (`cst_ir.spl`); forced-unparsed audit path (`--force-unparsed
--reason`, never public_ready by default); enforced v2 state model with
legacy-v1 name mapping (`state_model.spl`); dual-byte content model
(`dual_byte.spl`); metadata DB on textual SdnDatabase+WAL — deliberately NOT
rt_sqlite emulation; WAL replay needs a prior schema snapshot, so
crash-before-first-save loses pre-snapshot rows (`metadata_db.spl`); symbol
entities via interim .spl structural scanner (`symbol_entity.spl`, P-06
query-pack hookup TODO). Ledger 42/42 done (week-6 rows due 2026-10-13,
signed step scripts SCV-IMPL-{E-04,E-05,P-04,P-05,G-02,G-03,B-03,B-04,I-03}).
B-01 remains blocked on sj repair.
