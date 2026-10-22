# Phase 3 release integration checkpoint

Status: BLOCKED QUALIFICATION; INCOMPLETE IMPLEMENTATION; NOT LANDED.

Review checkpoint: draft PR https://github.com/ormastes/simple/pull/3083 targets
release_phase3. Initial work commit is `4daae8a1315`; it preserves source drafts,
not a verified release candidate. The feature is not complete merely because
its recovered files are now on a GitHub work branch.

The requested compiler stage is now Phase 3. Local work branch
`work/traceability-release_phase3-20261011` is based on fetched GitHub release_phase3
revision `20f619fe31baa4decbe40f6d367fb5e4f115bbd8`. The existing isolated
worktree path retains its historical phase2 name. Recovered source is preserved
in the draft PR. The runner bridge was reconciled directly against this branch;
the old conflict-staging candidates were not copied into the worktree.

The user corrected the exact GitHub destination to `release_phase3`; its branch
API confirmed the revision above. The earlier inventory only matched release/
prefixes and missed this name. Target clarification is resolved. The worktree
was switched directly onto this baseline rather than replaying unrelated
release/1.0 commits; the feature's own design was preserved through a scoped
stash and its recovered source restored. No release merge is claimed.

## Observed Phase 3 prerequisites

- `rel-p3run/PROBLEMS.md` reports a Phase 3 LLVM build at source `d7e46c6650a`
  exiting 139 during bootstrap entry MIR lowering. It reports no object files
  and no produced Phase 3 `simple.exe`.
- The newer `rp3d-20261011/attempt-04.status` is terminal, exit 64, source
  `40b21e6b60498858d163d8f64813f89623f07d12`. Its log rejects canonical release
  version authority, parent Stage 2 admission and runtime provenance before
  dependent qualification. This is not a feature source failure or PASS.
- The executables found in the earlier stage3 storage are explicitly Stage 2
  runtime authorities or prior-attempt copies, not proof of a Phase 3 compiler.

No bootstrap build was relaunched, no other session's bootstrap source was
modified and no Phase 2 or Rust seed executable was relabeled as Phase 3.
The exact-target item2-phase3 verification lane subsequently launched attempt
01. Its stdout reports Rust seed/runtime preparation; stderr then reports
`portable-lock: ownership check failed reason=owner-start` and
`Rust authority lock ownership was lost`. The progress state records `exit-1`.
It stopped before producing the required compiler. This is a bootstrap
prerequisite failure, not a failed feature test or evidence that feature source
cannot compile. That separate lane's files and processes were not modified.

The same compiler lane's attempt 02 stopped at disk preflight before Cargo:
`FAIL — disk-space(18GiB<20)`. Current C: free space is approximately 13.6 GiB.
No other build volume is mounted. The user was asked to free at least 6 GiB or
provide a build volume. No unrelated build outputs were deleted. An admitted
source-matched Phase 3 compiler remains unavailable.

## Source checkpoint after continuation

- Git provider now captures immutable tree/blob bytes, resolves the tree from
  a frozen commit identity, validates budgets and hashes exact Git blob frames
  using shared SHA-1/SHA-256 implementations. Selector `index` freezes the
  selected index with `write-tree`, records a git_index subject without a fake
  commit identity, and reads blobs from that frozen tree. Aggregate blob content
  is checked against the caller's byte budget. Its process lifecycle still
  requires real failure-path execution tests before admission.
- Existing CLI structured reports now use the native SDN codec; JSON modes
  are rejected. Legacy worktree discovery is explicitly labeled unverified
  and admission-ineligible. Exact-snapshot graph CLI wiring remains unfinished.
- The SDN-only trace-batch codec is connected to opt-in framework events,
  structured sidecar ingestion, exact-path runner record attachment and the
  existing test database writer. Trace events share the owner's summary save,
  retain actual failed/pending outcomes and are stored as unverified. Invalid
  batches and replayed file scopes are rejected. Started-only prefixes remain
  interrupted observations rather than disappearing from history. Frozen run
  planning, source/binary/config provenance, mandatory feature SDN/Markdown
  reports and aggregate command failure handling remain unfinished.
- `direct-env-runtime-guard.shs --working` and `--staged` each passed once;
  the candidate diff passed whitespace checks. Exact Git inventory found zero
  executable `_spec.spl` files under `doc/06_spec`. These are static checks,
  not a production verification PASS.
- Authored provider/hash/SDN report unit scenarios are unexecuted. All full
  feature acceptance criteria and NFR execution evidence remain pending.
Resolve a source-bound admitted Phase 3 compiler/provider before running the
feature scope. All 20 requirements, 40 acceptance criteria and NFRs remain
required; implementation and evidence gaps from verification_status.md remain.

## Current unqualified continuation

The source CLI now accepts exact index/Git selection with explicit paths and
uses the shared extractor/resolver through snapshot_pipeline. The scoped SDN
preview retains its roots and explicitly refuses admission eligibility. Trusted
commit/push/remote/audit profiles remain unavailable and return infrastructure
failure. This route has not been compiled or executed with the admitted target.

Structural identity binds actual content hashes, blob references, visibility,
registered paths and every policy record; candidate identity separately binds
generation. Empty selected roots and unsupported closure claims are rejected.
The Git provider keeps path whitespace and hashes its local repository identity
so spaced/Unicode checkout paths do not become invalid graph IDs.

New pure run-plan reconciliation rejects empty feature plans and matches actual
file/case observations to independent intent. Runner transport checks now cover
zero-result, partial and cached rows; persistence precedes document generation.
No pre-dispatch durable plan or provenance admission exists yet. New source and
regression specs remain authored/unexecuted. Astra reviewed these seams and found
the identity/empty-plan/partial-transport issues that were corrected in source.

The feature-owned SDN declaration now records the 20 requirements, 40 planned
criteria and current source/document responsibilities. It has no test definitions
or execution records; native parser verification and policy registration remain
mandatory. No full system criterion, NFR or release-readiness PASS is claimed.

## Shared build observation, 2026-10-11

The previously observed unrelated grouped Phase 3 collector process (PID 27976)
was absent on the subsequent authoritative process query. Its recorded receipt
at `C:/dev/simple/build/phase3-grouped-candidate-plan-20261011/compile-cycle5-corrected/receipt.env`
reports `reason=timeout`, `native_exit_status=124`, `cleanup_status=reaped`.
The child log stops at worker-spawn startup. This observation supplies no
runnable or source-matched compiler qualification for the traceability lane.
The build belongs to another session and was not restarted or cleaned here.
