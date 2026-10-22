# N2 fast-feedback evidence contract

Status: pure evidence contract drafted and Astra static review found no P0/P1; its focused spec remains unrun because the self-hosted Simple runner exited 139 and this session's verification cap is exhausted. Live runner and selected N2 targets remain unverified. Merge owner: Codex root. Keep this lane separate from the dirty hook/workflow/runtime files.

## Frozen interface before sidecar implementation

- New pure module `src/app/build/scheduler/n2_feedback_evidence_v1.spl` and focused `test/01_unit/app/build/scheduler/n2_feedback_evidence_v1_spec.spl`.
- `N2FeedbackFixtureV1`: `kind`, `fixture_sha256`, `candidate_tree`, `source_revision`, `outgoing_ref_manifest_sha256`, `runtime_sha256`, `toolchain_sha256`, `policy_sha256`, `host_id`, `warm`, `outgoing_ref_count`, `required_gate_digest`, `required_gate_count`.
- `N2FeedbackSampleV1`: `ordinal`, `fixture_sha256`, `candidate_tree`, `source_revision`, `outgoing_ref_manifest_sha256`, `runtime_sha256`, `toolchain_sha256`, `policy_sha256`, `host_id`, `warm`, `wall_ms`, `outcome`, `executed_gate_digest`, `executed_gate_count`, `peak_memory_kind`, `peak_memory_bytes`, `bytes_transferred`, `queue_ms`, `admission_ms`, `action_ms`, `transfer_ms`, `publication_ms`, `action_cache_hits`, `receipt_cache_hits`.
- `N2FeedbackDecisionV1`: `admitted`, `reason`, `sample_count`, `p50_ms`, `p95_ms`, `p99_ms`, `numeric_target_met`. Export `check_n2_feedback_evidence_v1(fixture, samples)`.
- Exact kinds: `staged-hook`, `pre-push-one-ref`, `warm-preflight`. Require exactly one outgoing ref for pre-push and zero for the other kinds; warm=true for warm preflight. Candidate tree and source revision are lowercase 40/64 hex; digests are lowercase SHA-256. The canonical zero-ref manifest is zero bytes with SHA-256 `sha256_text("")`; non-push fixtures require that digest, while a one-ref fixture rejects it. The collector must hash the exact retained ref-update bytes for the one-ref manifest. Bounded host identity. Require 20–1024 ordinal 1..N complete samples from one fixture/tree/source/ref manifest; every outcome `pass`, executed gate digest/count equal required gate digest/count, and numeric phase/resource fields nonnegative and bounded. Memory kind must be `private`, `unique`, or `pss`; `rss`, `cgroup`, `unknown`, and absent metrics reject. Never infer a full invocation from a numeric sample alone.
- Compute nearest-rank P50/P95/P99; compare P95 with selected thresholds from `n2_latency_numeric.spl`: staged hook ≤5000 ms, one-ref pre-push <10000 ms, warm preflight <60000 ms. A numeric miss returns an explicit non-admitted decision. A true decision is still copied-evidence consistency, not authenticated live N2 PASS.
- Manual flow names: `step("Pin fast-feedback fixture")`, `step("Run complete hook samples")`, `step("Validate mandatory gate and memory evidence")`, `step("Compare N2 percentiles")`. Setup/checker names: `given_n2_feedback_fixture_v1`, `check_n2_feedback_receipt_v1`. A live runner gap must fail explicitly.

## Parallel ownership

| Lane | Files | Acceptance |
|---|---|---|
| Astra | Read-only review of V4 process observation and N2 contract | Identify unavailable metrics and unsafe assumptions. |
| Pure implementation | Only the new module and focused spec above | Fail-closed raw sample admission and percentile boundaries. |
| Merge owner | This plan and N2 TODO | No false N2 PASS; keep hook, workflow and runtime ownership intact. |

## Runtime handoff

The existing V4 process facade supports pinned executable/cwd, bounded output, monotonic timestamps and direct-child/tree RSS. It currently lacks private/unique/PSS memory, proven descendant containment and stdin delivery; it cannot itself qualify whole-hook N2. A future pure-Simple runner must retain raw receipts, exact Git/ref/policy/runtime identity, executable and script snapshot, mandatory gate rows, one-ref stdin fixture, real cancellation and complete cleanup. It must use a qualified process provider or report `INCOMPLETE`; RSS cannot be renamed PSS. The selected requirement remains [N2](../../02_requirements/nfr/dist_build_scheduler.md).

Astra's final review also requires the protected collector to prove that the fixture digest binds source, outgoing refs, runtime, toolchain, policy, host and independent invocations. Mixed private/unique/PSS samples retain their metric labels and measurement methods; they are not interchangeable memory measurements. A shuffled-duration percentile fixture and source/ref mismatch cases are included in the unrun focused spec.

The copied-sample checker now requires runtime, toolchain, policy, host and
warm-state equality for every sample as well as source/ref equality. This
prevents a visibly mixed set from producing one admitted percentile, but it
does not authenticate the collector or prove independent full invocations.
