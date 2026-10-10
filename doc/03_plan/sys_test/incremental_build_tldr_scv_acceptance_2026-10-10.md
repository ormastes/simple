# Executable acceptance plan

This matrix specifies real-owner scenarios. A row is not executable coverage until its `.spl` file exists, calls the owner, and receives qualified execution evidence. All newly planned rows are UNRUN. Existing closed diagnostic lanes are not restarted.

Canonical spec root: `test/03_system/compiler/incremental/`. Manual mirror: `doc/06_spec/03_system/compiler/incremental/`. Pure contract cases may use `test/01_unit/lib/source_change/`. Never put executable `.spl` under the manual tree. Use actual release `std.spec.*` (exports `step` and `expect`) and `step("...")`; built-in matchers only. Shared helpers are `capture_exact_generation`, `apply_observed_transaction`, `verify_remaining_summaries`, `assert_exact_receipt`, `assert_phase_counters`, and `assert_closed_owned_tasks`. Helpers must call real owners; unavailable capability is a failing/blocked scenario, not a no-op implementation.

| Requirements | Spec group / actual operation | Happy path | Edge case | Refusal/failure case |
|---|---|---|---|---|
| 001–003 | `standalone_owner_spec` / compile via embedded gateway | Compile with no SCM/runner | Delete optional daemon/index/notes, fresh fallback | Broken external cache never supplies unverified bytes |
| 004 | `snapshot_identity_spec` / existing snapshot capture | Complete canonical inventory | Same bytes on another branch/rebase preserve semantic root | Missing row, mixed generation or changed discovery witness rejects |
| 005 | `source_change_adapters_spec` / IDE, SCV, Spipe adapters | Same actual transition has equal digest | Undo/redo, save boundary, atomic multi-file rename | Claimed intent differs from captured result |
| 006 | `source_change_recovery_spec` / shared service | Valid exact event chain | Lost cursor/watch overflow produces reconciled diff | Wrong base/snapshot/sequence never admits hint as proof |
| 007 | `source_change_codec_spec` / actual codec | SDN and SMET golden roundtrip on 3 hosts | Unknown optional frame skipped, multibyte/CRLF retained | Critical unknown, overflow, overlap, checksum and torn frame reject |
| 008 | `source_change_wal_spec` / existing SCV DB/WAL | Atomic batch survives reopen | v1 migration and empty history remain readable | Crash before checkpoint/replay cannot stamp complete |
| 009 | `checkpoint_roots_spec` / canonical domain identities | Exact matching roots admit | Same content different timestamp/actor equal | Producer/schema/grammar/config/provider mismatch misses |
| 010 | `project_coverage_spec` / freshness verifier | All expected module and init headers verified | Explicit valid empty scope has separate proof | Omitted/new/deleted module, missing header or partial scope rejects |
| 011 | `semantic_invalidation_spec` / compiler queries | Private/comment edit retains equal interface | Static variant preserves independent old variant | New overload/trait/impl/aspect/generic-body/negative query invalidates |
| 012 | `checkpoint_delta_spec` / actual baseline selection | Verified Git/SCV delta checks only changes | Same-source rebase associates new commit | Nonancestor/absent CAS/incomplete sparse inventory forces fallback |
| 013 | `freshness_association_spec` / notes and SCV writer | Exact verified revision attached | Dirty index/worktree/buffer remain distinct | Changed HEAD/tree/config cannot receive prior receipt |
| 014 | `freshness_writer_spec` / shared mutation lease | Serialized merge of independent typed receipts | Remote unavailable leaves valid local association | Expected-old ref conflict cannot overwrite foreign receipt |
| 015 | `freshness_status_spec` / status/history reader | Valid receipt shown without compiler launch | Lost tiny hint index finds earlier valid checkpoint | Forged hint/removed object yields unknown or regeneration |
| 016–017 | `postbuild_dag_spec` / runner journal/TestRunner | Binary publish then remaining jobs, mandatory join | Test fails after binary, binary retained | Pending or stale generation never qualified success |
| 018 | `conditional_commit_spec` / explicit SCM commit job | Authorized frozen index commit after gates | Concurrent branch move returns stale | Default no commit, no add-all/amend/force or unrequested push |
| 019–020 | `parse_owner_reuse_spec` / frontend + actual header producer + compile/test | One retained authoritative parse serves TLDR and compile | Restore serialization after reset; TestRunner same key | Source change/newer stale header or invalid parse never reused |
| 021 | `smf_layout_parity_spec` / real pack/directory/hybrid loaders | Equal semantic and link results | Lazy section load and archive fallback | Missing/tampered section fails without duplicate publication |
| 022 | `bootstrap_closure_spec` / actual admitted producer | Hello builds reachable libraries only | Distinct front/HIR/MIR/runtime/link producer versions | Unbound provider or incomplete source projection blocks publication |
| 023–024 | `singleflight_recovery_spec` / actual parent and worker APIs | Equal key has one owner and one publish | Parent confirms death, requeues exactly once | Foreign stale lease, result-B-for-A, crash before seal cannot poison owner |
| 025 | `incremental_perf_parity_spec` / fresh vs reused compiler | Same outputs/diagnostics, recorded counters | Cold and warm separate fixtures | Overbudget/duplicate parse or tree walk records failure, no headline PASS |
| 026–027 | `incremental_status_spec` / real CLI and SDN stats | Separate binary/freshness/test/SCM states | Remaining set empty, valid nonvacuous checkpoint | Synthetic counters or unknown job verdict never report verified |
| 028 | `incremental_vertical_slice_spec` / complete integration | Edit→SCV WAL→compile/TLDR→receipt→status | Missing metadata falls back to full verified capture | Late source change leaves new generation pending, old association exact |

Additional mandatory matrices: allocation failure/conversion truncation; UTF-8 byte boundaries and CRLF; path case/normalization collisions; file add/delete/rename; staged/unstaged/untracked/unsaved; symlink/gitlink/generated input authority; lost worker and concurrent process singleflight; secrets absent from event metadata; deletion of all optional derived stores; remote artifact trust and retention edges.

Acceptance admission pins source/import closure, actual linked provider, fixture/data hashes, target/config, bounds and exact counted verdicts. Each new feature gets at most three verify/fix cycles; criteria already green are not rerun unless changed evidence invalidates their qualification. Source-only seed checks are labeled diagnostics. Native smoke/check compiler/lib/MCP/LSP, environment-facade audits, production SPipe/docgen zero-stub gates and release review remain required and UNRUN.

## Evidence update for this plan revision

The first new V3 index diagnostic consumed one of three cycles: nine structural cases executed, seven passed and two failed on the seed byte-array iteration fixture path; no skips or drops. The independent full-topology job timed out at 90 seconds with no counted verdict, so executed/pass counts are unknown. The Job closed. This does not establish native/provider/performance qualification or whole-topology success. The original SCV thirteen-case lane remains closed; its eight passes and five setup failures are not replayed.

The first SourceChange primitive cut has fifteen unexecuted cases. Its original `app.spipe.testing` fixture import has no matching module in the selected release. A preserved successor fixture uses the real `std.spec` owner before any preparation or execution. Production primitive source is unchanged; no alias module was added.
