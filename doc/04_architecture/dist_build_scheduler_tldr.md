<!-- codex-architecture -->
# Distributed build and fast feedback — TLDR

Proposed architecture for distributed builds, faster local/GitHub feedback, exact CI admission, submodule/branch policy, Clang integration and Simple Container/Orchestrator workers across supported operating systems. Numerical NFR thresholds remain pending user selection.

## Core shape

- Compiler common owns versioned immutable action/input/result contracts. App adapters own scheduling, hooks, native providers and repository policy.
- Scheduler owns DAG and attempts; node agents own process trees; workers return candidates; only the broker publishes against the current fence.
- Reuse existing native identity, dependency manifests, receipts and CAS. Unknown input closure disables reuse.
- The drafted first slice passes one verified producer archive through `native-build --input-manifest` into an executable consumer and keeps outputs private until validation. Multi-archive link order and full closure-bound reuse remain blocked.
- An app adapter composes action/attempt contracts with existing strict Pod/Job and container-provider contracts. Placement distinguishes physical host, execution OS and compiler output target; unsupported isolation classes never become plain process successes. Only hosted Linux OCI has a concrete provider today.
- One gate registry binds staged/pushed/integration candidates to current policy and checker evidence. Gitlinks remain authoritative pins; Ninja retains native graph ownership.
- Signed local build evidence can shorten eligible GitHub work only after a base-owned verifier checks the exact candidate, signer scope, inputs, toolchain and artifact bytes. The required GitHub status still runs, and uncertain evidence falls back to the full build. Existing receipts do not yet cover build jobs.

## Operational notes

- Startup loads bounded configuration and indexed ledger/toolchain state; hot requests avoid full-tree rescans.
- Action inputs/toolchains invalidate build identity; checker/policy changes invalidate admission receipts. Attempt IDs and nodes do not change semantic keys.
- Ordinary pushes already skip advisory rows unless `MUST_CHECK_ADVISORY=1`. Measure complete push time, not only the blocking budget.
- Remote execution requires authenticated scope, bounded SDN control and verified binary payloads. Late revoked attempts cannot publish.
- Known nonzero worker exits close only as `action-failure-unclassified` after durable terminal observation, versioned failure proof, exact status replay and diagnostic retention. Missing evidence reserves the fence; failed outputs never publish. Deterministic source diagnosis needs a separate evidence contract.
- Clang strict/complex/none policy applies on warm and cold paths. Grouped providers require isolated-reference equivalence and measured benefit.
- Verify real two-node and Linux OCI execution, cross-OS admission, input mutation, stale fences, forks/base drift, submodule pins and native policy changes. Drafted modules lack passing focused specs on the stale self-hosted test runner; cross-OS providers and performance remain unqualified.

## Open next

- [Full architecture](dist_build_scheduler.md)
- [Delivery plan](../03_plan/compiler/build_system/dist_build_scheduler_2026-09-25.md)
- [Agent ownership](../03_plan/agent_tasks/dist_build_scheduler_2026-09-25.md)
- [Current executor](../../src/app/build/targets/target_executor.spl)
- [Archive inventory](../01_research/domain/simple_clang_header_cache_2026-09-25/README.md)
