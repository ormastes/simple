# Workaround retirement at the next rebuild

Status: implementation review packet; native tests UNRUN. The preparation and
admission API is implemented, but the existing bootstrap source-preparation
entrypoint does not yet call it. No current workaround is automatically removed.

## Selected contract

The user requested linking workaround tags, bug state and Git commits so that a
later rebuild applies the root fix before automatically retiring its workaround.
`fix_available` is not `fix_applied`: a fetched object or a bug's fixed status
cannot authorize source changes. This extends the recover-only policy in
`doc/07_guide/tooling/bug_linked_workarounds.md`; an old marker alone retains its
old, non-automatic meaning.

REQ-WR-001: a versioned SDN record names workaround ID, canonical bug ID, kind,
full workaround/fix commits, root-fix proof task, original-form removal test,
required backends, and exact reviewed path/before/after fragments. Existing
SDN quoting/parser helpers own the format; no new database engine is added.

REQ-WR-002: the chosen committed rebuild revision must contain both commits.
The producer's admitted source revision must contain the fix too. Missing
lineage blocks retirement; this API does not fetch, cherry-pick, reset, revert,
or mark a global bug done. A caller may apply a reviewed fix in its authorized
next-rebuild flow, then invoke preparation on the resulting committed revision.
The actual canonical Stage2 receipt is reopened: artifact and source authority
hashes are verified by their existing admission owner. Every source file changed
by the root-fix commit must occur with the exact fixed bytes in that producer's
authority. A new source revision string cannot relabel an old binary. Version 1
conservatively blocks later edits to those fix files, deleted source files,
non-text source changes and fixes with no `src/` changes until a reviewed record
and suitable admission adapter exist.

REQ-WR-003: validated root-fix task receipts are required before preparing an
inverse. The owner creates a new exclusive transaction and detached worktree,
never accepts an existing destination, and verifies fragment provenance against
the actual workaround commit and its parent. Only exact unique fragments are
replaced. Every fragment matches before any candidate file is written. Changed
or ambiguous hunks retain the input and return blocked-retirement. A failed
private write leaves an unpublished candidate for inspection.
Containment uses resolved host path identities, not lexical path prefixes.
Fragments already present unchanged across the workaround commit are refused.

REQ-WR-004: original-form tests run on the private candidate, with their working
directory, outputs and caches outside its source directory. Existing TaskRunner
parent validation owns authenticity, actual process closure, result parsing and
positive registered case counts. This API requires all selected backends,
exact task/source/producer identity, validated success, zero process/task exits,
no signal and a reaped tree. Caller-constructed booleans are not production
proof. The integration specs deliberately use synthetic receipts to test the
admission contract, not to certify a compiler fix.

REQ-WR-005: admission rechecks lineage, the complete Git binary diff, registry
pin, root proof, and absence of all untracked files (including ignored files).
It writes an immutable source-scoped retired receipt with test result/log
digests. Identical admission is idempotent; changed candidates cannot borrow
old evidence. The result identifies HEAD plus exact inverse patch/source
digests, rollback revision, registry and producer. No unrelated portion of a
mixed workaround commit is reverted.
Assume-unchanged, skip-worktree and other nonordinary Git index entries are
rejected before computing source identity. The canonical producer receipt is
reopened again at final admission.

REQ-WR-006: only then may the existing source-preparation owner freeze the
returned derived checkout and generate normal SCV/manifest/task identities.
Changed dependency identities naturally invalidate affected entries. Preserve
all other valid cache objects; never clear caches or forge compatibility.
Retirement failure is an independent source-preparation result: existing
frozen builds continue and retain their outcomes. Global bug state and the
derived workaround index remain separate from this exact-source receipt.

## API and pending integration

`app.bug.workaround_retirement` owns strict record/proof/hunk transformations.
`app.bootstrap_builder.workaround_rebuild.workaround_rebuild_prepare_v1` creates
the candidate after root-fix proofs. Its source digest is SHA256 over the
versioned domain, committed revision and exact binary diff. The task factory
must use that digest when requesting the original-form proof; it cannot relabel
an older SCV or existing receipt as this identity.

`workaround_rebuild_admit_v1` returns the candidate source only after removal
proofs. `native_group_phase2_source_snapshot` and its existing admission owner
are the intended downstream consumers, before source freeze, not worker hot
paths. Production wiring still needs an explicit selected-registry input,
authoritative bug-transition event and producer-admission lookup, two proof
tasks through the existing runner, durable blocked-event handling, and normal
source freeze after admission. Do not add a second scheduler or mutate the
currently running bootstrap. Native qualification and this wiring are required
before claiming automatic end-to-end retirement.

Configuration restoration is a distinct kind. This source adapter rejects it;
the actual configuration owner must validate the default, generation and
equivalent removal tests. An unknown AV root fix cannot authorize restoration.

## Bounds and validation

Maximum 128 hunks, 1 MiB total fragment metadata, 8 MiB per changed file,
32 MiB changed-source batch, 16 MiB Git diff, and eight backend proof rows.
No full-tree scan is added to a compiler worker. A detached worktree is a
one-time next-rebuild preparation cost, not a warm compile optimization.
RSS/elapsed measurements and native execution remain UNRUN.

`test/02_integration/app/workaround_retirement_spec.spl` covers strict schema,
exact hunk conflict/ambiguity, unrelated edits, empty/failed/unvalidated/unreaped
and wrong-source proof, missing backend, fetched-but-unapplied fix, producer
lineage, input checkout refusal, mixed commits, idempotence and stale evidence.
It retains isolated Git fixtures for inspection. A real corrected-producer
run of the linked original-form tests remains mandatory for each inventory
entry, independent of these contract tests.
Additional negatives cover an old producer source authority despite a new
revision argument, ignored source files, both hidden-index flags, fragments
untouched by the linked commit, and a real directory under an ancestor alias.

Owner: memory_perf_lane. Final reviewer/integrator: root. Additional sidecars:
N/A. No release qualification or automatic bug closure is claimed.
