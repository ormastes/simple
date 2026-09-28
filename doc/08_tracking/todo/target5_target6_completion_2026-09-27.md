# Target 5/6 completion

Status: ACTIVE; production qualification remains OPEN.

PR #1932 merged the focused Stage2 bootstrap/runtime repairs into `main` at
`0dbb2c1691a442829737507dc8d1d2a970bbf7bf`. The continuing Target 5/6
lane is `codex/target56-next`; the merged PR did not complete either target.

Continuation note (2026-09-28): the isolated current-source Stage2 candidate
now passes its full native build and positional hello-world frontend smoke
after repairing dynlib lifetime state inference, backend diagnostics, exact
Cranelift O2 selection, and the raw-string UTF-8 SFFI boundary. Its compiler
test matrix is still open: default delegated rows require owner-supplied
MC/DC-off waiver fields. The in-process matrix's five-second RSS observer
budget held, but its full CLI build failed in three owner update closures and
one POSIX constructor body. The owners now use direct typed state mutation
under their original mutexes; a focused 48-file no-stub native build passed.
The POSIX constructor now compiles in a focused 49-file no-stub native build,
but its close path hits the old capsule's named `rt_collection_remove` trap.
The runtime dispatcher and pure-Simple twin have source repairs. A fresh
Stage2 runtime capsule now passes verification, and its no-stub native
owned-device create/close probe exits zero with owner counts returning to
zero. The pure-Simple shadow gate and full compiler matrix still need
verification. See
`doc/08_tracking/bug/target56_stage2_positional_hello_world_silent_exit_2026-09-28.md`.
The runtime trap and next proof are tracked in
`doc/08_tracking/bug/target56_stage2_runtime_collection_remove_trap_2026-09-28.md`.
The pre-rebase snapshot-registry state repair in
`sffi/dynlib_snapshot_registry_v1.spl` passed its focused 37-file no-stub
bootstrap build and the full Stage2 native build, positional hello-world
smoke, and runtime capability proof. The rebase retained main's independent
Simple-side descriptor-list fix in that owner. A focused no-stub native build
of the rebased source compiled 37 files with zero failures; its probe exited
zero with missing-library refusal. The in-process Stage2 compiler-test
matrix failed at its full CLI link after 1,828 seconds with unresolved
GPU/SQLite/SDL/Metal and other reached symbols. A focused same-bundle linker
trace proves the host-gpu path selects a generated core-C archive and hosted
rlib, omitting the frozen native-all archive. That core-C archive defines none
of the 178 missing names; native-all defines 117 but is not a complete or
appropriate optional-provider fix. The later test rows were blocked. See
`doc/08_tracking/bug/target56_stage2_full_cli_optional_runtime_link_2026-09-28.md`.
Detailed attribution is in
`doc/09_report/compiler/target56_stage2_link_argv_attribution_2026-09-28.md`.
Stage4 and the production size/startup/performance cohorts remain unavailable.

The user accepted the matched-startup C reference for the Linux 1.05x size
limit during an earlier session closeout. That closeout did not convert the
diagnostic probes into a Stage4, SPipe, native performance, or release PASS.
The remaining technical items below remain active; see
`doc/09_report/compiler/target56_user_closeout_2026-09-28.md`.

Owner lane: `codex/target56-next` (PR #1932 merged). This TODO carries the unfinished work
from `doc/09_report/compiler/target5_strict_core_hello_2026-09-27.md`,
`doc/09_report/compiler/target6_cold_hir_batch_2026-09-27.md`, and
`doc/08_tracking/bug/target56_isolated_current_source_verification_blockers_2026-09-27.md`.
The isolated changes are groundwork and diagnostics, not production acceptance.

## Next-session TODO

- [x] Link a current-source pure-Simple Stage4 diagnostic compiler through the
  dynamic runtime lane, run a hello `--check` smoke, and retain a paired static
  diagnostic size/startup/RSS comparison. The 30-pair Linux ARM64 result is in
  `doc/09_report/compiler/target5_stage4_dynamic_vs_static_diagnostic_2026-09-29.md`.
- [x] Measure a current-source core-C hello with explicit Linux LLD and a
  diagnostic 30-pair Python startup/RSS cohort. Its 14,560-byte stripped ELF
  clears the absolute size cap; matched C and admission gates remain open.
  See `doc/09_report/compiler/target5_current_source_hello_lld_diagnostic_2026-09-29.md`.
- [ ] Build and admit an ABI-matched **current-source pure-Simple Stage4**
  compiler and runtime in this isolated lane. Preserve the phase-bound cache,
  record binary/source hashes, require `SIMPLE_NO_STUB_FALLBACK=1`, and resolve
  the closure stall and missing runtime symbols in the blocker report. The
  latest standalone-entry attempt is blocked by an old Stage2 builder's SQLite
  ABI validator and nondeterministic K1 composition binding; its hosted static
  diagnostic reaches an empty-MIR AOT failure. See
  `doc/09_report/compiler/target5_stage4_hello_entry_diagnostic_2026-09-29.md`.
- [ ] With that authority, run a current-source release-small Simple hello and
  a paired matched-startup C hello. Check exact output, retained symbols,
  <=15,360 bytes, <=1.05x matched C, empty NoGC/provider traces, and the
  30-sample development (100-sample release) startup/RSS cohort. The C-authored
  6,504/6,368-byte pair remains diagnostic only.
- [x] Run a focused Target 6 cold/warm/edit/delete Git-event native fixture
  with explicit cursor arguments through the production bridge. The newer
  Stage2 binary passes; see
  `doc/09_report/compiler/target6_cold_git_refresh_native_probe_2026-09-28.md`.
- [ ] Inspect a larger Git event batch before publication and run the
  production fixture on an admitted current-source Stage4 worker; do not
  repeat the three failed historical Stage2 aggregate workarounds.
  Finish the typed TLDR/SMF producer and graph publication, replace the
  binding-only index, then run the SPipe and native cold/warm/edit/SCC/variant
  time/RSS cohorts with the normalized-sum rule.
- [ ] Run the full Target 5 demand-load/Phase 7 matrix and Target 6 verification
  gates. Close the technical TODO only after a `STATUS: PASS` report; the user's
  session closeout is not a production qualification.

## Target 5 — kernel and extension demand loading

- Produce an ABI-matched current-source pure-Simple Stage4 compiler and runtime
  authority. Resolve the bootstrap failures in the blocker report without
  treating the historical Stage2 binary as release evidence.
- Finish metadata-only optional-provider registration and first-use loading.
  Prove no-import hello maps and initializes zero optional providers, while
  each excluded feature remains usable on first demand.
- Prove exact runtime/link closure for kernel, extensions, aspect packs, and
  native roots. Keep explicit `SIMPLE_LINKER` precedence while qualifying the
  Linux size-mode LLD selection on current source.
- Run the BS7 matched cohorts and Phase 7 one-binary/dynload rows. Require
  Linux stripped hello <=15 KiB **and** <=1.05x matched-startup, same-toolchain C, accepted
  startup/RSS budgets, 30 development or 100 release samples, and empty
  forbidden/optional-provider traces. The historical LLD diagnostic was
  13,944 bytes versus 4,864-byte bare C hello (2.87x); this remains advisory.
- Verify the plain-literal print lowering in a current-source Stage4 hello build:
  confirm the binary no longer retains `rt_string_new_literal`,
  `rt_to_string`, or `rt_literal_intern_table`; then measure paired size,
  startup, and RSS cohorts. The C-entry direct-writer probe is only
  directional evidence (5,152-byte ELF). A same-wrapper, same-root C user
  object probe is 9,168 bytes versus the historical Simple ELF's 13,944;
  it still misses the 1.05x C ceiling by 4,061 bytes and is not completion
  evidence. A controlled link without the historical builder's unnecessary
  `rt_function_not_found`/`rt_string_bytes` roots is 6,584 bytes, still 1,477
  bytes over the ceiling; current Stage4 already derives symbol roots from
  the final object closure, so this is attribution, not an unmade linker fix.
  Review argv and startup/runtime roots with exact closure proof.
  A C-bootstrap argv fast-path probe removed an allocation but enlarged its
  stripped microbinary by 152 bytes; the edit was reverted because the
  current pure-Simple core already stores argv without that allocation.

## Target 6 — persistent compile index

- [x] Prevent a stale binding-only index publication from replacing a graph
  generation after a concurrent writer wins. The pointer CAS has focused
  native and SPipe evidence in
  `doc/09_report/compiler/target6_package_index_binding_cas_2026-09-28.md`.
- [x] Apply warm multi-event inventory batches without one full-inventory
  rebuild per event. A 30-sample no-stub native fixture improves both p95
  time and peak RSS; serial-equivalence and atomic-rejection probes pass.
  See `doc/09_report/compiler/target6_warm_inventory_batch_2026-09-28.md`.
- Build a real cold TLDR/SMF producer from frozen SCV inventory and typed HIR.
  A pure graph assembler and inventory-bound index builder now live in
  `src/compiler/80.driver/cache/cold_hir_package_drafts_v1.spl` and
  `package_module_index_builder.spl`. They require caller-supplied typed
  HIR/SMF and archive receipts, bind a configuration variant into the V1
  root identity, and refuse incomplete source coverage. The actual cold
  compiler producer, generation publication, driver compatibility markers,
  and current-source execution remain open. HIR lowering currently visits
  `ctx.sources` (the reached compile closure); a producer must prove complete
  coverage of the frozen inventory, or define and admit an exact package-scoped
  inventory partition before it may publish this generation. The builder
  retains inventory entries once and stores only scalar source indices in its
  lookup table.
  The concrete producer/receipt ownership gap is mapped in
  `doc/09_report/compiler/target6_cold_graph_producer_boundary_2026-09-27.md`.
  The executable AOT SMF writer cannot supply typed export sections or
  per-module receipts; emit those from HIR rather than deriving placeholder
  digests from the combined code image.
  The first typed ABI section now emits actual canonical HIR bytes and a
  matching digest. The package export builder now packs real caller-supplied
  section bytes in canonical order and validates the complete payload against
  offsets, extents, and digests. The cold graph assembler now requires those
  bytes and the ABI section to match its typed-HIR seed before drafting a
  package index. Complete the other semantic sections and
  their artifact receipts before connecting this producer to index publication;
  run its new tamper scenario on a current-source worker.
  A versioned reverse-reference section now derives actual bytes from the
  reached graph and is checked against the SMF directory and TLDR receipt;
  run its canonical-order and stale-edge scenarios on that worker too.
- TLDR digest admission and SMF section order now compare bytes rather than
  native text handles. The shared canonical identity comparator also reads
  bytes in place instead of allocating two byte arrays per comparison.
  Qualify these checks and the warm/cold time-RSS effect on a current-source
  worker before treating the producer as admitted.
- Replace the binding-only empty index with a validated module/package graph,
  variant identity, exact reverse edges, reached SCC schedule, and complete
  action/archive receipts. Route compile, check, bootstrap, native-build,
  MCP/LSP, and daemon requests through one pinned catalog owner; remove warm
  closure scans. The existing warm package route now uses the shared bytewise
  heap sort for selected module and package identities instead of native text
  `<` plus quadratic selection/deduplication. Its closure walk now tracks
  queued modules in a lookup table. Archive routing now groups selected entry
  positions once, avoiding two full-generation scans per selected package
  while storing only integer links and package heads/tails. Qualify closure
  order, p95 time, and max RSS on the current-source worker.
  CLI snapshot admission now refuses to overwrite a stale nonempty graph with
  its temporary empty binding generation. The full graph producer still needs
  to rebuild and publish an exact successor after that refusal; the system
  spec now requires preservation of the prior graph on stale admission.
- Qualify the new atomic inventory/cursor `CURRENT` record on a current-source
  runtime. The isolated source now validates filesystem events before publish
  and writes the inventory digest plus Git/filesystem cursor in one pointer
  rename, with a bare-digest legacy reader. The historical Stage2 diagnostic
  native build timed out before an executable was produced. Prove failed
  rename, overflow, event loss, cross-process concurrent writers, cold rebuild, legacy
  migration, and replay recovery without Git or source mutation.
- The Git name-status bridge now rejects malformed, unknown, and quoted rows
  instead of advancing the event cursor past omitted source changes; a unit
  spec covers those cases. Run that spec on a current-source test worker and
  extend the same fail-closed coverage to cold `ls-files` and untracked paths.
- The SCV journal cursor now counts newline-terminated records rather than
  the trailing empty split element. It hashes the exact consumed byte prefix,
  so appending a new record does not falsely report a rewritten journal; a
  unit spec covers append, pending-event replay, truncation, and bad cursors.
  Qualify this on the current-source runtime before admitting warm refresh.
- Journal event rows now require the writer's exact `kind`, `path`, and
  `related` field names, a nonempty path, and a complete record envelope.
  Malformed rows reject the batch before cursor publication; the cursor spec
  includes rejected rows and a valid non-filesystem record.
- Produce and run a current-source test worker for the Git and journal specs.
  The three bounded Stage2 build attempts reached a core-C/GPU link mismatch
  and then missed the required hosted-runtime archive directory; see
  `doc/09_report/compiler/target6_test_worker_build_2026-09-27.md`.
- The shared SCV translator now rejects unknown/unpaired filesystem events
  before publication and removes a source renamed to a non-source path.
  Behavioral unit cases were added; run them on the current-source worker
  before accepting the event-admission path.
- An explicit cold refresh now rebuilds a complete inventory from the listed
  source events and publishes a successor generation, dropping paths absent
  from that listing. The CLI's cold inventory listing includes both `src` and
  `test` even when the current snapshot selects only one; warm replay remains
  incremental. Cold refresh now rebases a stale journal cursor from the full
  Git listing while warm refresh continues to reject rewritten rows. A unit
  spec covers a disappeared source, and a disposable-Git integration spec
  covers journal recovery. Run both on a current-source worker before marking
  cold rebuild complete.
- Close the untracked-deletion authority gap before allowing warm snapshot
  reuse: `doc/08_tracking/bug/scv_untracked_delete_reuses_stale_snapshot_2026-09-27.md`.
  The isolated cursor now binds `src` and `test` untracked membership digests
  and refuses warm reuse after a membership change; the disposable-Git
  integration case includes untracked deletion. Qualify current-source
  behavior, old-cursor migration, and warm p95/RSS before closing this bug.
  The existing warm `ls-files --others` traversal remains a separate Target 6
  zero-scan cutover gap.
- Cold refresh now derives the inventory and untracked membership cursor from
  one tagged Git listing instead of two independently timed listings. Run the
  disposable-Git cold/warm case on a current-source worker and prove concurrent
  directory changes cannot publish an invalid source/content binding.
- Run current-source SPipe and native performance cohorts for cold, warm,
  private edit, public edit, SCC, and variant cases. Require exact outputs,
  p95 time and max RSS hard budgets, plus the normalized time/RSS sum rule in
  the optimize skill and guide. The historical cold-HIR batch result
  (normalized sum 0.181595) is diagnostic only.
- The interface/action archive reader now validates lowercase digest bytes
  and sorts dependency digests canonically in O(n log n). Run an archive
  admission case on a current-source worker; the producer and receipt cutover
  remain open.
- The historical Stage2 native scheduler probe panicked with
  `direct-edge-missing:module.000:module.001` on a 64-module chain. Three
  fixture/check cycles produced the same result. The temporary fixture was
  removed and the production scheduler was left unchanged; diagnose this
  under an ABI-matched current-source authority before optimizing scheduling.

Completion requires a `STATUS: PASS` verify report. Stop after three
verify/fix cycles per feature and retain failing logs under `build/mini_builds/`.
