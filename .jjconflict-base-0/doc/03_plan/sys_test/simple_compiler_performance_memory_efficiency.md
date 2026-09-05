<!-- codex-design -->
# System Test Plan — Simple Compiler Performance and Memory Efficiency

## Scope

End-to-end evidence for REQ-001..REQ-025 and NFR-001..NFR-015. Static design is not PASS evidence. Tests use an admitted self-hosted pure-Simple binary; Rust seed/source-string/test-only reimplementations are forbidden.

## Canonical artifacts

| Surface | Executable | Manual |
|---|---|---|
| Operator flow | `test/03_system/app/compiler/feature/simple_compiler_performance_memory_efficiency_spec.spl` | `doc/06_spec/03_system/app/compiler/feature/simple_compiler_performance_memory_efficiency_spec.md` |
| Transform integrity | `test/02_integration/compiler/optimizer_transform_integrity_spec.spl` | mirrored `doc/06_spec/02_integration/...md` |
| Diagnostics | `test/02_integration/compiler/perf_diagnostic_contract_spec.spl` | mirrored manual |
| Shared facts/summaries | `test/02_integration/compiler/perf_facts_summary_spec.spl` | mirrored manual |
| Fact budgets | `test/05_perf/compiler/compiler_perf_facts_budget_spec.spl` | mirrored manual |
| Tool hot paths | `test/05_perf/compiler/compiler_tool_hot_path_spec.spl` | mirrored manual |
| Profiles/curves | `test/05_perf/compiler/compiler_perf_profile_curve_spec.spl` | mirrored manual |

## Frozen visible flow

1. `Load the effective optimizer pipeline`
2. `Reject dishonest active transforms`
3. `Analyze one function with shared performance facts`
4. `Report actionable performance and memory diagnostics`
5. `Preserve semantics while applying a proven transform`
6. `Compare compiler and runtime evidence against the baseline`

Frozen helpers: `setup_optimizer_integrity_fixture`, `setup_perf_diagnostic_fixture`, `check_effective_pipeline_status`, `check_perf_facts_reuse`, `check_perf_diagnostic_record`, `check_semantic_differential`, `check_perf_budget`. Alternate sidecar vocabulary is rejected.

## Traceability

| Group | Positive | Boundary | Failure/unknown |
|---|---|---|---|
| REQ-001..005 | effective plan + valid sentinel/verifier | non-candidate, idempotence, backend | identity/empty active pass, unavailable fact, verifier fail |
| REQ-006..009 | one revision and indexed typed facts | edit/invalidation + COLL snapshot | stale/reparse/unknown fact |
| REQ-010..012 | catalog positives + known costs | fixed-small and cost variants | unsupported op and bounded Unknown |
| REQ-013..015 | fact reuse + proven escape/COW | targeted invalidation/lost uniqueness | unsafe promotion/clone rejection |
| REQ-016..018 | pure plan/scalar transform | legal-unprofitable/idempotent | alias/effect/control/numeric rejection |
| REQ-019..022 | SCC/.sperf/.sprof-v2/curve | invalidation/disabled profile | timeout/stale/single-timeout reject |
| REQ-023..025 | measured repair/provenance/links | cold-scan distinction/stage boundary | missing blocker, Rust fallback, broken trace |

Every requirement receives positive, boundary/suppression, and failure/unknown executable observations across the focused specs. NFR-003..007/010..013 require measured receipts, not prose.

## Evidence and pass criteria

- Behavioral: typed production records, exact spans/reasons, exit/stdout/stderr.
- Structural: verifier and pass/fact/cache counters from runtime owners.
- Semantic: optimized/unoptimized equality over all observable channels.
- Performance: same admitted binary, fixture/provenance, distributions, peak RSS, domain counters.
- Profile: valid optional records and disabled-path evidence; ranking never legality.
- Documentation: docgen complete, zero stubs after implementation, visible claim boundaries and REQ links.

Before endpoints exist, scaffolds fail with `assert(false)` and cannot count as coverage. Missing binary/backend/baseline/profile, timeout, stale/corrupt evidence, or unsupported stage is FAIL/BLOCKED, never skip/PASS.

## Execution order

1. Record binary path/hash/stage/provenance and baseline once.
2. Check/run focused integration specs after each owned slice stabilizes.
3. Run umbrella flow once after focused evidence is current.
4. Run fixed perf scripts once after implementation and compare the same baselines.
5. Generate each mirrored manual once; require complete/0 stubs.
6. Run compiler/lib/MCP/LSP checks, lint/duplicate/facade guards, and layout guard once in final verify.

Hard cap: three distinct fix/verify cycles per feature slice; no identical failed or unchanged green rerun.

## Manual policy

The six frozen steps remain visible in order. Setup and large adversarial matrices fold; rejection reasons, provenance, incomplete rows, and claim boundaries remain visible. Executable source is folded below the operator flow. `/root` performs final manual-quality review.
