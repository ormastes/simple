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

## Post-Wave-3 (2026-08-26)
Wave 3 (SCV-IMPL E-06, E-07, P-06, G-05, D-01, I-04, D-03, D-04, G-04) is
landed and green (closeout sweep 2026-08-26; regressions all held, incl.
mvp 11/11, merge 5/5, symbol-entity 3/3, incremental-parse 9/9,
file-identity 8/8; gates mission-critical PASS with 6 profile rows, crash
harness 9/9, restore drills 6). New capabilities: warm status with a REAL
I/O counter at the stat/read choke points — warm clean is 0 stats/0 reads/no
parse, one change is at most one stable read (`src/lib/scv/warm_status.spl`);
bulk-update generation that holds the coalescer and reconciles once through
warm status (`bulk_update.spl`); entity query packs for simple/python/rust on
one engine — line-structural rules, not grammars; symbol_entity now delegates
to the simple pack (`query_packs.spl`); interface/HIR fingerprints reusing the
compiler's `compile_interface_digest` + `implementation_digest_of` as
`syntactic_interface_id` / `normalized_impl_hash` — `typed_hir_hash` is
honestly `unavailable`, no typed-HIR extractor exists, TODO(SCV-IMPL-G-06)
(`hir_fingerprint.spl`); structural-roots diff over REAL P-05 CST roots keyed
by revision+ContentId via `scv cst-store` — the first producer for the P-05
root store, interim `cst-spl-1` builder until grammar-backed roots land
(`diff.spl`, `structural_match.spl`); refactoring relations as many-to-many
lineage edges with bounds (MAX_PAIRS=512 / CANDIDATES_PER_UNIT=64 /
AMBIGUITY_MARGIN=50), ties never accepted (`refactoring_relations.spl`);
`scv diff --view graph` hunks <-> entities <-> ops (`edit_graph.spl`);
identity-aware merge via per-commit EntityId maps, jj stays conflict authority,
rename-vs-rename limited by the linear I-02 store (`identity_merge.spl`);
default/strict/mission_critical profiles pinned in `.scv/profile.sdn`, strict
and mission_critical refuse forced_unparsed publication (`profiles.spl`).
Findings: the long-standing "merge 1/5" red was a `scv_text_to_u8` all-zero
hash collision (every text-derived id collided by length; fixed in
`store.spl` with `value.bytes()`, seed-side `for ch in text` defect still
OPEN, pre-fix repos have length-collided ids); merge-commit `parents:`
separator inconsistency (merge.spl fixed to space-joined; integrity_view/
recover/maintenance/integrity still split on "," — OPEN); mtime is
second-granular so warm status only trusts reads whose post-read stat matches
the pre-read stat. Ledger 51/51 done (week-7 rows due 2026-10-27, signed step
scripts SCV-IMPL-{E-06,E-07,P-06,G-05,D-01,I-04,D-03,D-04,G-04}). B-01/B-02
remain blocked on sj repair (`sj --version` rc=139 on 2026-08-26).

## Post-Wave-4 (2026-08-26)

Wave 4 landed ten items across four lanes: E-08 watchman adapter
(`src/lib/scv/watchman_adapter.spl`, protocol-complete, verified against a
replay endpoint — watchman is absent on this host), E-09 editor IPC and P-07 nvim
`scv/editor/v1` protocol (`editor_ipc.spl`, `nvim_protocol.spl`; transport is a
pipe-spool because the `rt_unix_socket_*` externs are shape-mismatched
against the Rust runtime's (ptr,len)/out-param ABI — listen/connect return
-22 EINVAL, recv core-dumps; bug record
`doc/08_tracking/bug/rt_unix_socket_extern_shape_mismatch_2026-08-26.md`),
G-06 interface-driven build invalidation (`build_invalidation.spl`;
syntactic_interface_id drives downstream invalidation in SCV metadata;
dependency-closure invalidation is reported `unavailable` until a real
compiler dependency model exists, so the comment-only codegen skip stays
BLOCKED — file-level invalidation only), D-05/D-06/D-07 region
merge + merge validation + conflict v2 (`region_merge.spl`,
`merge_validation.spl`, `conflict_v2.spl`; unparsed remainder publishes as
`validated_partial`, never promoted), I-05 calibration corpus + oracle and I-06 identity
corrections CLI (`identity_corrections.spl`, scv identity
link|unlink|split|merge|trace; the one-rename-per-EntityId ceiling is now
emitted as `entity_identity_ambiguous` instead of guessing a winner), and
B-05 shadow-write trigger (`shadow_write.spl` + a config-gated hook in
`store.spl`, OFF by default; crash harness re-verified green on the edited
store). Acceptance sweep 2026-08-26: watchman 6/6, editor-ipc 6/6,
nvim 7/7, build-invalidation 5/5, region-merge 5/5, merge-validation 5/5,
conflict-v2 4/4, identity-corrections 3/3, shadow-write 3/3;
`check-scv-identity-precision.shs` PASS 100.0% on the 34-case corpus
(`test/fixtures/scv_identity_corpus/`); regressions held (mvp 11/11,
merge 5/5, dual-write 4/4, file-identity 8/8, event-source 4/4,
hir-fingerprint 3/3, incremental-parse 9/9). Ledger 61/61 done (week-8 rows
due 2026-11-10, signed step scripts
SCV-IMPL-{E-08,E-09,P-07,G-06,D-05,D-06,D-07,I-05,I-06,B-05}, WOTS leaves
59..68).

## Post-Wave-5 (2026-08-26) — last ungated wave

Wave 5 landed the final two ungated plan items, D-08 and B-06. All ungated
items in `doc/03_plan/app/tools/scv_complete_impl_plan.md` are now done;
what remains is gated only (B-01/B-02 blocked on an `sj` segfault rc=139,
B-07 a 6-12 month shadow soak, B-08 human sign-off).

**D-08 is landed ADVISORY-RED — read this before trusting a merge.** The
28-case corpus (`test/fixtures/scv_merge_corpus/`) and its gate
`scripts/check/check-scv-merge-corpus.shs` are wired and the gate's selftest is
green, but the gate FAILs at **3 missed real conflicts**:
`22_cpp_ifdef_condition_vs_body`, `24_cpp_ifdef_else_split`,
`26_cpp_rename_edit_preprocessor` — the merger claims clean merges across
divergent preprocessor branches. Filed as
`doc/08_tracking/bug/scv_merge_silently_merges_across_divergent_preprocessor_branches_2026-08-26.md`.
Do NOT baseline these misses. The `SCV-IMPL-D-08.shs` step script exits PASS
because it checks artifacts + selftest, not the full ~50-minute scan.

**B-06 (green):** `pack_v2.spl` reachability-aware `pack-write-v2r` /
`pack-verify-v2r` reusing `scv_gc_roots_reachable` from `maintenance.spl` by
import (never a copy), `reach <id>` payload lines skipped by the pre-existing
v2 reader (no format break, v1 reads spec-pinned), seeded-LCG `pack-fuzz-v2`
(64/64 corruptions detected, 0 silent decodes), `pack-soak-v2`
write/pack/gc-quarantine/fsck cycles. Spec 8/8. The 50-cycle soak did NOT
complete (20 cycles in budget; 50 projects to ~2500s, killed twice).
Perf: `gzip_compress` takes ~110s for 16KB and dominates pack write —
`doc/08_tracking/bug/scv_gzip_compress_dominates_pack_write_2026-08-26.md`;
the soak works around it with stored blocks. Measured but deliberately NOT
"fixed": `scv_append_bytes` alias-push 1ms vs concat 582ms.
Regressions held: scv_mvp 11/11, scv_merge 5/5. Ledger 63/63 done (week-9 rows
due 2026-11-24, signed step scripts SCV-IMPL-{D-08,B-06}, WOTS leaves 69..70).
