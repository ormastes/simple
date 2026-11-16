# DAE-05 B1 source ownership and handoff

Status: SOURCE_REVIEW_PENDING / NOT_RUN, 2026-11-15. Root owns integration/landing.
Implementation: current Sol lane. API/source/manual reviewer: independent Astra.
Sidecars: N/A for this bounded slice; no new agents or runtime campaigns.

Root approved the journal assessment port, common data contract, private fixed
artifact I/O, real Host status consumer and necessary strict-controller consumer
compatibility. Astra accepted the ID-only input, bounded actual-owner references,
deterministic sampling and explicit examined/total/omitted/Incompleteness contract.

Source files are:

- `src/lib/common/contracts/distributed_operation_assessment_v3.spl`
- `src/lib/common/task_runner/distributed_operation_assessment_io_v3.spl`
- `src/lib/common/task_runner/distributed_operation_journal_v2.spl`
- `src/lib/nogc_sync_mut/orchestration/host_operation_retention_assessment_v3.spl`
- `src/lib/nogc_sync_mut/orchestration/host_local_command_v1.spl`
- `src/lib/nogc_sync_mut/orchestration/controller_dispatch_owner_v2.spl`

The controller change is the specifically approved compatibility addition:
allow only an optional bounded non-authorizing `retentionAssessment` field,
preserve old required fields/authority checks and reject unrelated unknowns.
No admission baseline, native export, process/env facade or runtime was changed.

Unique specs/manuals cover real owned journal and canonical reservation payload
reads, caller errors without poison, sticky authoritative payload damage,
actual `host-status` consumption without provider commands, deterministic four-row
sampling and explicit omitted counts, legacy unavailable diagnostics, and pure
old/new strict-status compatibility. Pure status fixtures are not admitted native
identities or dispatch permissions. Scripted Container fixtures are not invoked
and do not qualify platform behavior. See the system-test plan and design.

Accepted R4 baseline: exact 22-file content hash
`e5e1a9c2e119e76fe9a17e6948e1dee6285e38639d16e02d6392749c47939310`.
Only the explicitly approved narrow journal change touches those accepted files.
The four untouched storage foundation files/provenance remain exact. Root
temporarily borrowed/restored all WIP for unrelated reviewed landings; no worker
Git stage/commit/push/rebase/branch switch occurred.

B1 was functional source batch 5. Final correction batch 6 preserves the managed
caller's existing Option cleanup.lock handling (unwrap Some, otherwise retain).
No assessment/consumer semantics or native foundation were changed by that fix.
The source-fix budget is now exhausted: no further correction cycles or budget
reset for B/C. Freeze exact files/hashes for Astra review and stop when accepted. No
compiler, seed, build, native/test, SPipe generation or performance run is allowed
under the exhausted campaign. Source acceptance cannot be reported as runtime
PASS, expiry activation, physical reclamation or full DAE-05 completion.

Integration uses only the final 13-file B1 delta. The inherited 34-file diagnostic
snapshot is not a replacement overlay for the managed branch. Preserve managed
store `origin_root`/`belongs_to`, newer admission/storage provenance and the
already-correct managed cleanup caller. Apply the narrow changes to existing
journal/Host/controller files against their actual reviewed parents; never copy
old foundation files from the worktree over the newer managed implementation.
