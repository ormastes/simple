# Runner memory aggregate overflow — 2026-10-28

Owner: shared-runner-memory lane; status: fixed, focused interpreter evidence.

The pure TestRunner worker-memory parser accepts multiple reservations whose
sum exceeds i64. Its caller sums those charges without checking overflow.
Current CLI limits constrain normal inputs; this is a public-helper boundary
regression and a prerequisite for sharing memory policy with build groups.

The repair rejects unrepresentable aggregate charges and moves strict
fit and conservative reservation arithmetic into common TaskRunner. Native
build groups retain byte units; TestRunner retains KiB. The common arithmetic
requires every argument in the same unit. OS probes, thread policy, fiber
progress overcommit and existing enforcement owners remain unchanged.

## Callers and evidence

`nogc_sync_mut/test_runner/test_runner_async.spl` calls `sample_worker_memory`
and `worker_memory_can_spawn`. An invalid nonempty-root snapshot returns an
empty charges array, so its existing cardinality check blocks admission.
The accepted snapshot's sum is representable; additional dispatch charges are
bounded by the common strict-fit predicate before spawn. Reservations for
missing child roots are retained until the owner reaps and removes them.

`app/bootstrap_builder/grouped_native_run.spl` and `phase_admission.spl` call
`native_group_process_budget_v1`, which now uses the same reservation-floor,
checked-add and strict-fit helpers in byte units. Its existing numeric bounds,
monitor overshoot, CPU check, commit-measured condition and refusal messages
remain intact. This is native build-group admission, not a new shared lifecycle
for `app/buildrunner/runner.spl` and TestRunner. RSS sampling is advisory
admission evidence; the platform watchdog/job/cgroup owners enforce limits.

Base: release `db3e7d` ancestry. Producer: existing Phase 1 generation
`aa58a24ebe00248b428d4507e5cb0c58ec497c28ec8b2a3ed71ec65d697f756c-ecd1ed1cbf3f68a7abc6c2f852358542fae0b6e2e66c88e5abfcd5ea22cb3d2b`
in `/Users/ormastes/wt/release-bootstrap-integration-20261025/src/compiler_rust/target/bootstrap.generations/`.
No Phase 2 rebuild occurred.

Run each spec separately with `SIMPLE_LIB=src <producer>/simple test <spec>
--mode=interpreter --assert-ran --no-cache --no-db --no-session-daemon
--sequential`. The runner refuses multiple file arguments in this lane; that
refusal is not a test verdict.

- Red `/tmp/shared-runner-memory-red.log`: 3 total, 2 passed, 1 failed;
  unrepresentable aggregate returned two maximum-i64 charges instead of `[]`.
- Green `/tmp/shared-runner-worker_memory_admission_spec.spl.log`: 3/3.
- Added descendant/missing-root regression:
  `/tmp/shared-runner-memory-parser-spec.log`: 4/4.
- Final bounded per-root expression:
  `/tmp/shared-runner-memory-final-spec.log`: 4/4.
- Common `/tmp/shared-runner-memory_admission_spec.spl.log`: 3/3.
- Existing `/tmp/shared-runner-grouped_native_process_policy_spec.spl.log`:
  11/11, including monitor floors/overshoot and memory/commit boundaries.
- Working direct-environment guard and whitespace check passed.
- Independent Luna review: no actionable P0/P1/P2; parent review still owns
  final admission. Native backend/platform qualification and full core/MCP/LSP
  checks are outside this focused interpreter receipt and remain unverified.

## Retained provider discrepancy

An initial refactor also replaced the per-root expression
`charges[owner] = charges[owner] + kib` with
`charges[owner] = task_memory_add_v1(charges[owner], kib)`.
The existing `simple run test/01_unit/lib/test_runner/worker_memory_probe.spl`
then reported `[4800, 400, 128]` instead of `[600, 128, 128]` in its first
snapshot assertion (`/tmp/shared-runner-memory-probe-restored.log`). Restoring
the original worker module passed the same probe
(`/tmp/shared-runner-memory-probe-baseline.log`). The explicit interpreter
scenario passed with the helper expression. An isolated one-element array
loop with the helper passed in run mode, so the discrepancy is not yet reduced
to indexed calls alone; the full worker parser/import closure is required by
the retained reproducer. The producer reports `hybrid-interp-splice` and a
bootstrap-seed warning in run mode. This is diagnostic provider evidence,
not qualified native validation.

The final change keeps the existing per-root arithmetic: row count <=16384
and each parsed RSS <=2^40 prove that sum <=2^54. Only reservation floors can
exceed that bound; their aggregate is still checked through the common helper.
With this bounded expression restored, the existing parser/admission/CLI probe
passes (`/tmp/shared-runner-memory-probe-sum-fixed.log`). The provider discrepancy
remains open for the compiler owner; reproduce by substituting the expression
above and running that existing probe on the named Phase 1 producer. No compiler
fix or native safety claim is made here.
