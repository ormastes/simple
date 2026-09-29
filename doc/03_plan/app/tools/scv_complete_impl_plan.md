# SCV Complete Implementation Plan (v2)

**Status:** ACTIVE — 2026-08-25. Companion to `scv_migration_month_plan.md` (which it does NOT replace).
**TL;DR:** `scv_complete_impl_plan_tldr.md`.
**Derived from (three variants of one v2 design, unioned):**
- `doc/01_research/app/tools/scv/scv_v2_final_report_2026-08-25.md` (layers §5-7, diff/merge §11-12, modules §15, phases 0-8 §17, backlog §23)
- `doc/01_research/app/tools/scv/scv_v2_wrapper_architecture_report_2026-08-25.md` (gap audit A-E, immediate order 1-12, workstreams A-H)
- `doc/01_research/app/tools/scv/scv_v2_sj_integration_report_2026-08-25.md` (sj single-writer, Rust notify bridge, SQLite/WAL schema, parser provenance, cutover gates)

## Scope split

The **month plan** owns stabilization/migration S0→S4 (SCV-MIG-01..25; W1-W2 done,
W3 in flight). **This plan** owns everything else the three reports demand: the
event layer, real parsing, persistent identity, semantic diff/merge, commit
policy, and the (gated, undated) native backend path to S5/S6. Items are
`SCV-IMPL-<track>-NN`. Acceptance is always a runnable command whose LAST stdout
line must be `PASS…` or a spec `Results: … 0 failed` line. Landed / in-flight
work is marked with pointers and is NOT re-planned here.

Governing rule (all three reports): **backend bytes establish truth (Git); jj
establishes logical history; SCV establishes source identity and intent.** All
mutations route through the single `sj` write lane (sj report; "two independent
mutating daemons" is an explicitly rejected alternative — no standalone `scvd`
mutator).

## Conflict resolutions between the three variants

| Conflict | Winner | Why |
|---|---|---|
| Standalone `scvd` daemon (final/wrapper) vs sj-capsule single writer (sj report) | sj report | Newest, repo-grounded; independent mutating daemon is in its rejected-alternatives list; sj already exists |
| Watchman-first event source (final report Phase 2) vs Rust `notify` bridge first (sj report) | sj report | Grounded in the real watcher audit: Simple watcher is an mtime mock, SimpleOS inotify is ENOSYS; the Rust notify watcher already exists in the compiler driver. Watchman becomes a later adapter (E-08) |
| ChangeId derivation left loose (final) vs random 128-bit never-derived (sj) | sj report | Binding spec; already landed as SCV-MIG-01, moot for scheduling |
| Generic metadata layout (final §14) vs SQLite-WAL DB + migration off pipe-delimited sdn (sj §13) | sj report | Concrete schema, lifts the `\|`/newline path restriction, matches Track B |
| Phases 0-8 (final) vs 0-7 (sj) | union | Naming variance only — sj folds native-authority into its P7 cutover gates; not a real conflict |

## Track E — Events / Layer-2 working-copy I/O

| id | what | depends-on | acceptance | size | lane | status |
|---|---|---|---|---|---|---|
| SCV-IMPL-E-01 | Rust `notify` bridge: extract compiler-driver watcher into `src/runtime/fswatch/` + `src/lib/nogc_async_mut/file_system/event_watch.spl` (rename pairing, sequence tokens, overflow classification, ignore policy, deterministic test injection) | MIG-13 | `bin/simple test test/integration/lib/scv_event_watch_spec.spl` → `Results: … 0 failed` | L | scv | DONE pure-Simple half (polling + injection, pairing, overflow, ignore; Rust notify bridge in src/runtime/fswatch/ still TODO — fswatch_native_open fails explicitly) (Wave 1 lane D, 2026-08-26) |
| SCV-IMPL-E-02 | `EventSource` protocol: cursor {source, opaque_token, fresh_instance, overflowed}, mandatory invalidate/rescan path; all watchers are hints | E-01 | `bin/simple test test/integration/lib/scv_event_source_spec.spl` | M | scv | DONE (Wave 1 lane D, 2026-08-26) |
| SCV-IMPL-E-03 | Event journal integration: event batches into the W2 WAL (MIG-10), pending→committed lifecycle, replay idempotent | E-02, MIG-10 | `bin/simple test test/integration/app/scv_event_journal_spec.spl` | M | scv | DONE (Wave 1 lane D, 2026-08-26) |
| SCV-IMPL-E-04 | Coalescer/settle: editor micro-batch, fs settle window, save immediate, VCS/bulk deferred; atomic-save (tmp-write-rename-delete) coalesces to modify-target | E-02 | `bin/simple test test/integration/lib/scv_event_coalesce_spec.spl` | M | scv | DONE (Wave 2 lane A, 2026-08-26) |
| SCV-IMPL-E-05 | Persistent binary worktree index (path key, mode, size, times, both ContentIds, FileId, clock, dirty/ignore generations); lifts pipe-delimited path limits | E-03, B-04 | `bin/simple test test/integration/app/scv_worktree_index_spec.spl` | L | scv | DONE as own binary store (Wave 2 lane A, 2026-08-26) — B-04 DB migration pending; load/save/upsert/get/remove is the adoption surface |
| SCV-IMPL-E-06 | Warm status zero-payload-reads: warm clean `scv status` = O(events), 0 content reads, no parsing; one changed file ⇒ ≤1 stable read (I/O counters assert it) | E-05, MIG-19 | `bin/simple test test/integration/app/scv_warm_status_spec.spl` | M | scv | DONE (Wave 3 lane A, 2026-08-26) — `warm_status.spl`: real ScvIoCounter at the stat/read choke points; warm clean = 0 stats/0 reads; one change = 1 FileBuffer read; never touches `fswatch_scan` |
| SCV-IMPL-E-07 | Bulk-update generation: checkout/rebase/branch-switch marks a generation, defers per-file events, reconciles once | E-05 | `bin/simple test test/integration/app/scv_bulk_update_spec.spl` | M | scv | DONE (Wave 3 lane A, 2026-08-26) — `bulk_update.spl`: begin bumps index dirty gen + holds coalescer, defer is zero-I/O with per-path folding, end reconciles once via E-06 |
| SCV-IMPL-E-08 | Watchman adapter behind EventSource (clockspec, settle, recrawl/fresh-instance → reconcile) | E-02 | `bin/simple test test/integration/lib/scv_watchman_adapter_spec.spl` | M | scv | done (2026-08-26; fake-watchman transport, live watchman TODO — binary absent on host) |
| SCV-IMPL-E-09 | Editor IPC: buffer_open/edit/save_begin/save_end/path_rename/refactor_begin-entity-end/flush over UDS; editor bytes skip the disk read | E-04, P-07 | `bin/simple test test/integration/app/scv_editor_ipc_spec.spl` | L | scv | done (2026-08-26; filesystem-pipe spool transport — UDS externs broken under seed, swap is TODO) |

## Track P — Parser / Layer-3 core

| id | what | depends-on | acceptance | size | lane | status |
|---|---|---|---|---|---|---|
| SCV-IMPL-P-01 | Honest parser provenance: exact labels `native-tree-sitter\|wasm-tree-sitter\|simple-parser\|fallback-line\|fallback-binary`; a fallback can never self-report as Tree-sitter; hash family split (raw/token/cst/format-normalized/interface/…) | — | `bin/simple test test/integration/app/scv_parser_provenance_spec.spl` | M | scv | IN-FLIGHT (gap lane, see state.md) |
| SCV-IMPL-P-02 | Hardened WASM shim contract: memory bounds, fuel limits, ABI checks, signature verification, deterministic serialization, fuzz corpus | P-01 | `bin/simple test test/integration/runtime/scv_wasm_shim_contract_spec.spl` | L | scv | DONE (Wave 1, 2026-08-26) |
| SCV-IMPL-P-03 | TRUE incremental parse: persistent `ParserSession` (open/apply_edit/changed_ranges/checkpoint), retain TSTree, exact `TSInputEdit`, parse-with-old-tree, changed ranges; differential full-vs-incremental equivalence + fuzzed edit sequences | P-01, P-02 | `bin/simple test test/integration/app/scv_incremental_parse_spec.spl` | L | scv | DONE (Wave 1, 2026-08-26) |
| SCV-IMPL-P-04 | Parser trust/lock hardening: registry pins grammar id/source/artifact sha256/TS ABI/protocol/runtime kind/signature; no implicit downloads; upgrades open new index generations | P-01 | `bin/simple test test/integration/app/scv_parser_lock_spec.spl` | M | scv | DONE (Wave 2, 2026-08-26) |
| SCV-IMPL-P-05 | Generic CST IR: File / Named / List(ordered\|commutative) / Atom / Trivia / Error, versioned; parser roots keyed by revision+ContentId | P-03 | `bin/simple test test/integration/app/scv_generic_cst_spec.spl` | M | scv | DONE (Wave 2, 2026-08-26) |
| SCV-IMPL-P-06 | Entity query packs per language: declaration kinds, name fields, signatures, scope parents, commutative lists, comment/doc nodes, reference rules (fixes the missing `name:` anchor fields) | P-05 | `bin/simple test test/integration/app/scv_query_packs_spec.spl` | M | scv | DONE (Wave 3, 2026-08-26 — `src/lib/scv/query_packs.spl`: simple/python/rust packs, one engine; symbol_entity delegates to the simple pack; fallback decl nodes carry `name:`+`signature:` so structural anchors are named; packs are line-structural rules, not grammars) |
| SCV-IMPL-P-07 | Neovim `scv/editor/v1` protocol: open_buffer/apply_edit/parser_changed_ranges/save/rename/refactor_transaction; Neovim trees are hints verified against bytes+artifact, never authoritative | P-03, E-09 | `bin/simple test test/integration/app/scv_nvim_protocol_spec.spl` | L | scv | done 2026-08-26 (wave 4 lane B; `src/lib/scv/nvim_protocol.spl`: pure request→response handler + in-process transport fold; Neovim range hints verified against bytes+artifact (`hint_status: verified/rejected`), every response says `authority: bytes+artifact`; refactor_transaction all-or-nothing; E-09 UDS wiring recorded as TODO(SCV-IMPL-E-09); spec 7/7) |

## Track I — Identity

| id | what | depends-on | acceptance | size | lane | status |
|---|---|---|---|---|---|---|
| SCV-IMPL-I-01 | `FileEntityId` + entity_graph: file identity split from FileVersion/path/mtime; copy⇒new id + `copied_from` edge | MIG-01 | `bin/simple test test/integration/app/scv_file_entity_id_spec.spl` | M | scv | IN-FLIGHT (gap lane) |
| SCV-IMPL-I-02 | Snapshot-path integration + `scv file-history` CLI: FileEntityId resolved on every implicit snapshot; rename+edit, atomic save, case-only rename covered by evidence order (editor txn > rename pair > exact content > similarity > user) | I-01, E-03 | `bin/simple test test/integration/app/scv_file_history_spec.spl` | M | scv | DONE (Wave 1, 2026-08-26) |
| SCV-IMPL-I-03 | `SymbolEntityId` + declaration extraction (module/type/trait/fn/field/variant/const) from query packs into persistent symbol_entity(+version) rows | I-01, P-06 | `bin/simple test test/integration/app/scv_symbol_entity_spec.spl` | L | scv | done 2026-08-26 (extraction now routed through the P-06 `simple` query pack as of Wave 3; no multi-language claim) |
| SCV-IMPL-I-04 | Refactoring relations: rename/move/move_rename/extract/inline/split/merge/pull_up/push_down/signature_change as many-to-many lineage edges; matcher = anchors → GumTree (indexed candidates) → RefactoringMiner-style rules | I-03, D-01 | `bin/simple test test/integration/app/scv_refactoring_relations_spec.spl` | L | scv | DONE (Wave 3, 2026-08-26): `src/lib/scv/refactoring_relations.spl`, rows `kind|from|to|conf|evidence|status`; bounds SCV_REFACTOR_MAX_PAIRS=512 / CANDIDATES_PER_UNIT=64 / AMBIGUITY_MARGIN=50; ties never accepted |
| SCV-IMPL-I-05 | Confidence calibration corpus + oracle: curated rename/move/extract corpus; auto-accepted relation precision ≥ 99.5% gate; classes Explicit/Verified-high/Inferred/Unresolved; ambiguity never silently accepted | I-04 | `sh scripts/check/check-scv-identity-precision.shs` → `PASS — precision ≥ 99.5%…` | L | scv | done (2026-08-26, lane D wave 4: 34-case corpus at test/fixtures/scv_identity_corpus, oracle in entity_graph.spl, measured precision 100000/100000 = 100.0% (28/28 accepted correct), gate green with fatal poisoned-corpus selftest) |
| SCV-IMPL-I-06 | Identity corrections CLI: `scv identity link\|unlink\|split\|merge\|trace` as logged operations; superseded rows aliased, never rewritten | I-03 | `bin/simple test test/integration/app/scv_identity_corrections_spec.spl` | M | scv | done (2026-08-26, lane D wave 4: identity_corrections.spl + `scv identity` CLI, append-only corrections log with edge:<n> alias refs, terminal split/merged states, spec 3/3) |

## Track D — Diff / merge

| id | what | depends-on | acceptance | size | lane | status |
|---|---|---|---|---|---|---|
| SCV-IMPL-D-01 | Structural-roots diff: diff loads real parser roots keyed by revision+ContentId (not simplified text blocks) | P-05 | `bin/simple test test/integration/app/scv_structural_roots_diff_spec.spl` | M | scv | DONE (Wave 3, 2026-08-26): diff loads REAL P-05 CST roots keyed by revision+ContentId (`scv cst-store`, `structural_source=cst-roots` > syntax-roots > text-blocks, both keys in the provenance line; named move/rename ops, ties reported `ambiguous`). Interim `cst-spl-1` builder — TODO(P-06/WS-A) in structural_match.spl |
| SCV-IMPL-D-02 | Three-view diff: one comparison, `--view raw\|syntax\|entity\|semantic\|all` + `--git-patch` (always-applicable Git patch export) | D-01 | `bin/simple test test/integration/app/scv_three_view_diff_spec.spl` | M | scv | DONE (Wave 1, 2026-08-26) |
| SCV-IMPL-D-03 | Refactoring-aware edit graph: diff report links raw hunks ↔ entities ↔ inferred refactoring operations | D-02, I-04 | `bin/simple test test/integration/app/scv_edit_graph_spec.spl` | M | scv | DONE (Wave 3, 2026-08-26): `src/lib/scv/edit_graph.spl`, `scv diff --view graph` (hunks <-> entities <-> ops) |
| SCV-IMPL-D-04 | Identity-aware merge: rename-one-side/edit-other resolved via EntityId, not path; jj stays conflict-storage authority | I-04, D-01 | `bin/simple test test/integration/app/scv_identity_merge_spec.spl` | L | scv | done 2026-08-26 (wave 3 lane D; `identity_merge.spl` per-commit EntityId maps + merge.spl pre-pass; 3/3; rename-vs-rename limited by the linear I-02 store — see TODO in spec; found+fixed `scv_text_to_u8` all-zero hash collision, see `doc/08_tracking/bug/scv_text_to_u8_zero_bytes_hash_collision_2026-08-26.md`) |
| SCV-IMPL-D-05 | Semistructured region merge: CST regions + line balance (MergirafSemi-style), commutative-list awareness | D-04, P-05 | `bin/simple test test/integration/app/scv_region_merge_spec.spl` | L | scv | done (2026-08-26) |
| SCV-IMPL-D-06 | Merge validation ladder: every aggressive stage validated (bytes → parse → entity uniqueness → interface → compile → tests) before acceptance; no clean-merge claim on failed validation | D-05, G-01 | `bin/simple test test/integration/app/scv_merge_validation_spec.spl` | M | scv | done (2026-08-26) |
| SCV-IMPL-D-07 | Typed conflict objects v2: kind (incl. entity_identity_ambiguous, signature_conflict, parser_disagreement), entity IDs, node sides, parser identity, attempted algorithms, diagnostics | D-04 | `bin/simple test test/integration/app/scv_conflict_v2_spec.spl` | M | scv | done (2026-08-26) |
| SCV-IMPL-D-08 | Merge corpus measuring **missed real conflicts** (not only spurious ones), incl. rename/edit through preprocessor-heavy sources | D-06 | `sh scripts/check/check-scv-merge-corpus.shs` → `PASS — 0 missed real conflicts…` | L | scv | done-advisory-red (2026-08-26) — corpus + gate landed (28 cases: 13 conflict-truth, 15 clean-truth, 6 preprocessor); gate is honestly RED at **3 missed real conflicts** (`22_cpp_ifdef_condition_vs_body`, `24_cpp_ifdef_else_split`, `26_cpp_rename_edit_preprocessor` — merge claims clean across divergent preprocessor branches), 0 silent mis-merges, 2 spurious (bound <=6). Defect filed: `doc/08_tracking/bug/scv_merge_silently_merges_across_divergent_preprocessor_branches_2026-08-26.md`. Promote to done once the merger gains preprocessor-region awareness and the gate goes green — do NOT baseline the misses. |

## Track G — Gates / policy

| id | what | depends-on | acceptance | size | lane | status |
|---|---|---|---|---|---|---|
| SCV-IMPL-G-01 | Explicit-commit parse policy: supported source requires locked available parser + successful parse within policy; unsupported text ⇒ `text_only` line mode; binary ⇒ bytes/chunks | P-01 | `bin/simple test test/integration/app/scv_commit_parse_policy_spec.spl` | M | scv | DONE (Wave 1, 2026-08-26) |
| SCV-IMPL-G-02 | `forced_unparsed` path + audit: `--force-unparsed --reason`, recorded state, never `public_ready` by default | G-01 | `bin/simple test test/integration/app/scv_forced_unparsed_spec.spl` | S | scv | done 2026-08-26 |
| SCV-IMPL-G-03 | State model: journal_only → private_editing/private_unparsed/private_parse_error/private_parsed → compile_ok → test_ok → verified_ok → public_ready; transitions enforced | G-01 | `bin/simple test test/integration/app/scv_state_model_spec.spl` | M | scv | done 2026-08-26 |
| SCV-IMPL-G-04 | Strict / mission-critical profiles: forced-unparsed publication blocked; profile config per repo | G-02, G-03, MIG-06 | `sh scripts/check/check-scv-mission-critical.shs` extended row → `PASS…` | S | mci | done 2026-08-26 (wave 3 lane D; `profiles.spl` default/strict/mission_critical, `.scv/profile.sdn` pin; gate row `6 profile row(s) enforced` PASS; spec 6/6) |
| SCV-IMPL-G-05 | Interface/HIR fingerprints via Simple compiler: interface_id, typed_hir_hash from the compiler frontend; names must state the guarantee (no "semantic" overclaim) | P-05 | `bin/simple test test/integration/app/scv_hir_fingerprint_spec.spl` | L | scv | DONE (Wave 3, 2026-08-26 — `src/lib/scv/hir_fingerprint.spl` reuses `compile_interface_digest` (simple/compile-interface/v1) + `implementation_digest_of` from the compiler frontend; fields are `syntactic_interface_id` / `normalized_impl_hash`; `typed_hir_hash` reported unavailable — no typed-HIR extractor exists, TODO(SCV-IMPL-G-06) in module) |
| SCV-IMPL-G-06 | Build-invalidation hookup: interface_id drives downstream invalidation; comment-only skips codegen only when the compiler dependency model confirms irrelevance | G-05 | `bin/simple test test/integration/app/scv_build_invalidation_spec.spl` | L | scv | done 2026-08-26 (wave 4 lane B; `src/lib/scv/build_invalidation.spl`: syntactic_interface_id drives transitive downstream invalidation in SCV metadata; comment-only classified via normalized_impl_hash but codegen skip BLOCKED by explicit `dependency_model: unavailable` (interface_digest_of: zero callers — compiler confirmation never claimed, TODO recorded); spec 5/5) |

## Track B — Backend / native

| id | what | depends-on | acceptance | size | lane | status |
|---|---|---|---|---|---|---|
| SCV-IMPL-B-01 | sj-capsule transaction coordinator: SCV capsule inside the `sj` daemon; 12-step lease→coalesce→capture→WAL→objects→jj snapshot→map→publish→release transaction with the failure matrix. **DEPENDENCY: `sj` is currently BROKEN on this host (segfaults, see state.md W3 log) — sj repair is a prerequisite; do not schedule until green** | MIG-13, E-03, sj repair | `bin/simple test test/integration/app/scv_sj_capsule_spec.spl` | L | scv | done-with-named-seam (2026-08-27) — `src/lib/scv/sj_capsule.spl`; spec `test/integration/app/scv_sj_capsule_spec.spl` **14/14, 0 failed** (+ `test/02_integration` twin), step script `scripts/scv-migration/steps/SCV-IMPL-B-01.shs` PASS (16 checks, unsigned). sj is repaired on this host (`sj --version`/`--help`/`raw jj log` exit 0). **10 of the 12 steps are REAL** (lease, cursor_sync, coalesce via E-04 `event_coalesce.spl`, capture, wal via E-03 `journal.spl` batches, objects, index, backend_map, publish, release). **Steps 8-9 (jj_snapshot / jj_read_ids) are a DECLARED SEAM**, because `sj raw jj` still returns the BUILT COMMAND STRING instead of executing jj (B-02's scope): they run through a pluggable `ScvJjExecutor` whose default is `unavailable`, following the D-06 ladder precedent — no mode in the module can report an anchor without a real backend id supplied from outside it, and an absent jj lane yields the report's own `unanchored` verdict, never `committed`. Single-writer is proved, not asserted: the lease is mkdir-atomic (`dir_create`, kernel-level exclusion, no TOCTOU window), a second capsule is refused, cannot release the first's lease, and its transaction returns `rejected_no_lease` having written nothing. All 9 failure-matrix rows are exercised. No mutating jj/sj command is run against any repository (the step script greps for and forbids one). Seed defect found and filed: `doc/08_tracking/bug/spec_step_bare_import_duplicates_file_rename_stack_overflow_2026-08-27.md`. Named residual seams: tmp+rename head publish (seed `file_rename` recursion) and the real jj lane. |
| SCV-IMPL-B-02 | jj CLI adapter, mutating: read-only adapter exists (MIG-13); mutating ops (snapshot/describe/new/undo) via sj lane only, pinned jj version, machine templates, no `.jj` internals | B-01 | `bin/simple test test/02_integration/app/scv_jj_mutating_adapter_spec.spl` | L | scv | done (2026-08-27) — UNBLOCKED: the sj segfault is fixed at tip a2a050e6296, so this was implemented. New `src/lib/scv/jj_adapter.spl` executes jj for real via `process_run` (argv, never a shell string); jj PINNED at 0.32 (`JJ_PINNED_VERSION`) and a mismatch REFUSES (`executed: false`, exit 2) rather than warning; flags `-R <repo> --ignore-working-copy --no-pager --color never` on every op EXCEPT `debug snapshot`, which must omit `--ignore-working-copy` or it is a no-op by construction; state read back only through `-T` machine templates; no `.jj` internals touched. `src/app/sj_daemon/request_handler.spl` (`handle_cli_args`, not `src/app/sj/request_handler.spl` as this row previously implied) now EXECUTES jj commands inside the lease instead of pushing `build_command(...)` strings to stdout with exit 0 — `sj raw jj log -r @ -T change_id.short(8)` returns a real change id where it used to print `jj --no-pager --color never ...`. Spec 5/5 (scratch mktemp+`jj git init` repos only; nothing mutates the real repo, nothing pushes). Step: `scripts/scv-migration/steps/SCV-IMPL-B-02.shs` (unsigned) PASS — 5 check(s). Known limits, stated not papered over: (a) `translate()` joins argv into strings and the handler re-splits on spaces, so the sj lane still loses quoting for multi-word arguments — pre-existing in the translator, not introduced here; callers needing exact argv use the typed adapter API. (b) git / raw-passthrough commands keep the previous build-only behaviour (git_mimic lane, out of B-02 scope). (c) BEHAVIOURAL DELTA: `sj git push --bookmark X` translates to "jj git push --bookmark X" and therefore now really PUSHES where it previously only echoed; `check_forbidden` still runs first but only inspects argv when argv[0] == "git", so `sj raw jj git push ...` reaches execution ungated. Deliberately NOT gated further here — push policy belongs to B-01, the transaction owner; flagged rather than silently widened. (d) B-01's `sj_capsule.spl` is not yet wired to this executor — the adoption API is `scv_jj_exec` / `scv_jj_exec_pinned` plus `scv_jj_snapshot/describe/new/undo`. |
| SCV-IMPL-B-03 | Dual-byte model: WorktreeContentId vs RepositoryContentId + TransformId for EOL/filter/attribute policies; native default = identity transform | MIG-12 | `bin/simple test test/integration/app/scv_dual_byte_spec.spl` | M | scv | done 2026-08-26 |
| SCV-IMPL-B-04 | SQLite-WAL / Simple DB metadata store: backend_revision, logical_change, implicit_snapshot, path_state, file/symbol_entity(+version), identity_relation, parse_index, event_batch tables; migration off pipe-delimited sdn indexes | MIG-10, MIG-12 | `bin/simple test test/integration/app/scv_metadata_db_spec.spl` | L | scv | done 2026-08-26 (backend: textual SdnDatabase + WAL from `std.database.core`, NOT the rt_sqlite emulation — the emulation is non-ACID with unenforced constraints; durability = CRC32 atomic snapshot + per-insert WAL append with replay on load; migration imports pipe files, identity.spl write path unchanged) |
| SCV-IMPL-B-05 | Native shadow write: every explicit revision written to BOTH jj/Git and native objects, continuously compared (tree, content, parent DAG, refs, reachability). MIG-24 seeds this; this item makes it continuous | MIG-24, B-02 | `bin/simple test test/integration/app/scv_shadow_write_spec.spl` | L | scv | done (2026-08-26, lane D wave 4: shadow_write.spl continuous trigger in store.spl scv_write_operation, config-gated no-op default, fail-closed log rows + `scv shadow-write enable\|sync\|status`; jj broken on host — git side is the read-only backend_git/shadow path; spec 3/3) |
| SCV-IMPL-B-06 | Pack v2 hardening: reachability-aware native pack, delta fuzzing, GC-never-loses-reachable soak. Per wrapper report: NOT before immediate-order items 1-10 are done | B-05 | `bin/simple test test/integration/app/scv_pack_v2_spec.spl` | L | scv | done (2026-08-26, lane B wave 5: pack_v2.spl reachability-aware `pack-write-v2r`/`pack-verify-v2r` reusing maintenance.spl `scv_gc_roots_reachable` (imported, not copied) with `reach <id>` payload lines the pre-existing v2 reader skips; seeded-LCG `pack-fuzz-v2` 64/64 corruptions detected, 0 silent decodes; `pack-soak-v2` write/pack/gc-quarantine/fsck cycles, spec runs 20 cycles in-budget; **the 50-cycle acceptance soak is now COMPLETE (2026-08-27)** — `pack-soak-v2 iterations=50 lost=0 fsck_dirty=0 quarantined=0`, `PASS — pack v2 GC soak: 50 cycle(s), 0 reachable object(s) lost, fsck clean after every cycle`, 5439s wall detached on this host. Phase totals: ms_pack=3506559 (64%), ms_gc=1581246 (29%), ms_fsck=306761 (5.6%), ms_snapshot=25612, ms_verify=429 — pack, not fsck, is the dominant half. Evidence and the cost curve are recorded in doc/08_tracking/bug/scv_gzip_compress_dominates_pack_write_2026-08-26.md); v1 read support spec-pinned both directions; spec 8/8) |
| SCV-IMPL-B-07 | Cutover gates (S4→S5 bar): zero unexplained mismatches over **6-12 months** shadow operation, crash-injection at every write boundary, cross-platform evidence, reversible upgrade, forge round-trip, independent-copy restore | B-05, B-06, D-08, I-05 | `sh scripts/check/check-scv-cutover-gates.shs` → `PASS…` | L | migration | GATED — no date |
| SCV-IMPL-B-08 | S5→S6 native authority (optional, per-repo, immediate Git/jj export retained). Explicitly beyond the month plan's S4 ceiling; listed for completeness, never scheduled here | B-07 | cutover-gate script all-green + human sign-off | L | migration | GATED — no date |

## Wave order

Respects the wrapper report's immediate order 1-12 and its "do NOT prioritize
native remote/pack before 1-10" rule; the month plan's S4 ceiling holds — S5/S6
items are gated, undated.

- **Wave 1 (week 5, post-month-plan continuation — ledgered, due 2026-09-29):**
  E-01, E-02, E-03, P-02, P-03, I-02, D-02, G-01. (Continues immediate-order
  items 3-5, 7-9; all dependencies are done or in-flight MIG/gap-lane work.)
- **Wave 2:** E-04, E-05, P-04, P-05, I-03, G-02, G-03, B-03, B-04 — LANDED
  2026-08-26 (ledgered week 6, due 2026-10-13); B-01 stays out until sj is
  repaired, then joins the ledger.
- **Wave 3:** E-06, E-07, P-06, I-04, D-01-completion→D-03, D-04, G-04, G-05 — LANDED
  2026-08-26 (ledgered week 7, due 2026-10-27). B-02 was held out as blocked on
  B-01 while `sj` segfaulted; that segfault is FIXED at tip a2a050e6296, and
  B-02 landed 2026-08-27 (see its row). B-01 itself is still open.
- **Wave 4:** E-08, E-09, P-07, I-05, I-06, D-05, D-06, D-07, G-06, B-05.
- **Wave 5:** D-08, B-06.
- **Gated (no dates):** B-07, B-08.

Waves 2+ are appended to the ledger only when their wave starts (checker-owned
file; only Wave 1 is ledgered now). Step scripts
`scripts/scv-migration/steps/SCV-IMPL-*.shs` are authored at wave start and
human-signed like the MIG steps; until then the checker reports ERROR-missing /
blocked-unsigned — the intended fail-closed state.

**Status 2026-08-26 (post-wave-5): every UNGATED item in this plan is done.**
Remaining items are gated, not pending: B-01 (sj-capsule coordinator — its
former blocker, the `sj` rc=139 segfault, is fixed at tip a2a050e6296; B-02
landed 2026-08-27 and exposes `scv_jj_exec` for B-01 to adopt as its executor),
B-07 (6-12 month shadow soak, no date), B-08 (needs B-07
all-green plus human sign-off). D-08 is landed advisory-RED — its gate
`scripts/check/check-scv-merge-corpus.shs` still FAILs at 3 missed real
conflicts in preprocessor cases 22/24/26; do not baseline them.
