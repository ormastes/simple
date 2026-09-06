# Unified lifecycle system-test plan

Executable owner:
`test/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle_spec.spl`.

| Scenario | Requirements | Oracle |
|---|---|---|
| Stable change and immutable revision identity | REQ-001 | Same seed gives same ChangeId; changed tree/parent/metadata changes RevisionId |
| Exact review/gate binding | REQ-003 | stale revision rejects approval and incomplete evidence rejects bundle |
| Observe-only protected planning | REQ-002, REQ-008, REQ-010 | valid policy parses; stale CAS/approval refuses; exact evidence yields dry-run steps only |
| Three-way provider projection | REQ-004, REQ-005 | disjoint edit pulls/pushes; concurrent edit creates durable conflict |
| Immutable release | REQ-006 | publication requires identity; published release rejects rewrite and permits withdrawal |
| Entity separation | REQ-007 | typed values retain distinct IDs/relations |
| Compatibility/portability | REQ-009, NFR-002, NFR-007 | DevHub compatibility help remains and lifecycle command has versioned output |

The manual-visible primary flow uses the five frozen step phrases in the SPipe
state. Edge and rejection scenarios may be folded. No remote provider, Git ref,
or tag is mutated by this system spec.

## NFR and fault-injection rows (added 2026-09-05)

Requirement text is `doc/02_requirements/nfr/scv_jj_git_devhub_spipe_unified_lifecycle.md`;
nothing below adds a requirement. Every row follows the fail-closed verdict
convention: `PASS — <n> … checked` with n > 0 / `FAIL — …` / `ERROR — nothing
was checked`, and a run that exercises 0 fixtures or records 0 measurements is
ERROR, never PASS. **Rows are plan text, not evidence.** The "Carrier / status"
cell names the executable spec that will hold the row and the stage that owns
it; until that spec exists and runs on a non-seed `bin/simple`, the row's
status is diagnostic at best (plan § "Path to Stage 0.5 done"). Source line
cites are against the committed blob at `e6446521cd3`; the `src/app/sj`
working tree was under concurrent edit when these rows were written.

| Scenario | Requirements | Oracle | Carrier / status |
|---|---|---|---|
| Fail-closed refusal of every unsafe input class | NFR-001 | The dry-run executor rejects, each with its own code and no admitted plan: malformed/missing identity (`SJ_IDENTITY_MISSING`, `src/app/sj/integrate_plan.spl:38-39`), stale CAS precondition (`SJ_REMOTE_STALE`, `:40-41`), stale or non-exact approval (`SJ_APPROVAL_STALE`, `:52-53`), incomplete gate bundle (`SJ_GATE_BUNDLE`, `:46-47`), missing manifest evidence (`SJ_GATE_EVIDENCE_MISSING`, `:106`), unknown or unparseable policy (`SJ_POLICY_UNKNOWN`, `:83`; `POLICY_INVALID` from `devhub lifecycle policy-check`), and — Stage 4 — a semantic projection gap returns a structured refusal, never a flattened object. One fixture per code; a run that reaches fewer than all listed codes is ERROR | `test/01_unit/app/sj/legacy_argv_dry_run_plan_spec.spl` (extend) + executor spec landing with plan step 3; Stage 0.5 → 2 → 4 |
| Every protected plan is fully attributed | NFR-003 | Each admitted dry-run plan and its persisted record name actor, authority, change/revision/base ids, policy digest, gate-bundle digest, and contain all four of `verify_scv_jj_git_tree_equivalence`, `compare_and_swap_integration_ref`, `verify_remote_revision`, `record_durable_audit_operation` (`integrate_plan.spl:54-64`); a record missing any field, or a step list missing any of the four, FAILs; the record read back through `devhub lifecycle inspect` is byte-equal to what was written | `test/01_unit/app/devhub/lifecycle_record_store_spec.spl` (extend) + executor spec; Stage 0.5 |
| Durable boundaries are idempotent or operation-linked | NFR-004 | Writing the same record twice with the same idempotency key through `lifecycle_store_write` (`src/lib/scv/lifecycle/store.spl:20`) yields one record with one digest; a differing payload under a reused key is a durable conflict, not an overwrite; Stage 4: partial remote work is reconstructible from the outbox/conflict record and `inspect --explain` names the boundary reached | `lifecycle_record_store_spec.spl` (extend); Stage 0.5 (store), 2 (lease/CAS), 4 (outbox), 7 (S0–S6) |
| Hot-path cost is measured, not assumed | NFR-005 | **Measurement row, not a threshold assertion** — the design defers numeric thresholds until a measurement pass has run. Record, for `sj plan`, `sj integrate --dry-run`, and `devhub lifecycle dry-run`: warm wall time, max RSS, count of `src/lib/**.spl` opens (strace), and subprocess count; assert only the structural clauses of the NFR: 0 subprocesses and no full-tree scan or repeated reread on the hot path without an explicit policy clause, and cache keys bind revision/tool/policy/environment digests. Every number is recorded beside `readlink -f bin/simple` + `stat` of the binary (`.claude/rules/commands.md`); a run with 0 recorded measurements is ERROR | new `test/03_system/app/scv/feature/..._lifecycle_perf_spec.spl` after the measurement pass; Stage 0.5 (local), 4 (provider hot path) |
| Credentials never leak into lifecycle surfaces | NFR-006 | Negative fixture: a sentinel credential placed in env, actor/authority text, and a remote URL never appears in any lifecycle object, `devhub/v1` JSON, persisted audit payload, or emitted URL; **paired control**: a fixture that deliberately leaks the sentinel MUST be detected by the same scan, else the scan is broken and the row is ERROR (`.claude/rules/testing.md` § Measurement traps) | executor spec (local surfaces, Stage 0.5); provider contract suite (Stage 4) |
| New pure-Simple code meets the quality bar | NFR-008 | Measured 2026-09-05 (`wc -l`, `grep`): every feature file under `src/lib/scv/lifecycle/`, `src/app/sj/{operation,integrate_plan,gate_manifest,lifecycle_policy,plan_main}.spl`, `src/app/devhub/{cmd_lifecycle,version_manifest,provider/lifecycle_*}.spl` is < 800 lines — largest is `lifecycle_policy.spl`, 364 at committed `e6446521cd3`, 384 in the concurrently-edited working tree; 0 files contain `TODO`/`FIXME`. NOT yet run: `sspec-maintain scan` over the feature specs — the oracle is that it MUST report 0 `SSDOC-ORA-001` blockers (no vacuous assertion), and until it has been run on this tree that clause is unmeasured, not passed. Deferred until the runner reports it: the 80% branch-coverage figure — it is NOT asserted here and no coverage number may be written into this row without a tool that produced it | file-size and stub checks measured (diagnostic); `sspec-maintain scan` pending; coverage blocked on runner support; every stage |
| Fault injection after each durable boundary | NFR-004, REQ-002 (research 1 §18.7) | Inject a failure immediately after each persistent boundary of the dry-run executor — after the manifest plan is computed but before `lifecycle_store_write`, and after the write but before the audit step is recorded — then re-run: the re-run is idempotent (same record digest, no duplicate), `devhub lifecycle inspect --explain` names the boundary reached, and no ref, tag, or remote is touched at any point; Stage 2/7 extend the boundaries to lease, CAS, publish and rollback. A run that injects 0 faults is ERROR | new `test/03_system/app/scv/feature/..._lifecycle_fault_injection_spec.spl`; lands with plan step 3, extended in Stage 2 and 7 |

