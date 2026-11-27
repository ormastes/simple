# Parallel delivery plan — 2026-11-03

Status: active implementation; neither all features nor compiler Phase 3 have passed.

This updates the [staged XRay plan](simple_xray_staged_implementation_plan_2026-11-03.md) and [earlier visibility plan](aspect_dynload_visibility_improvement_plan_2026-10-31.md). The supplied requirements are selected. The Linux LLVM → Linux Simple-owned → Windows Simple-owned order remains authoritative. Compiler bootstrap Phase 3 is a separate milestone from Windows XRay stage 3.

## Three concurrent tracks

| Track | Lead | Disjoint child scopes | Completion gate |
|---|---|---|---|
| Rebase and bootstrap | bootstrap_arm64_lead | Resolver repair; real native regression; crash evidence; producer/cache identity; pure-Simple parity | Exact rebuilt compiler compiles and runs required sanity; canonical full matrix; admitted Phase 3 lineage |
| ARM64/macOS bugs | bug_db_lead | ABI/native values; firmware/VirtIO/EL0; macOS GUI/Vulkan/process; tooling portability; database reconciliation | Real regression evidence per bug; native target evidence where required; correct DB state; reviewed merged PR |
| Cross-platform tracing | crosscompile_xray_lead | V1/config/event codecs; bounded session/collector; Linux LLVM adapter; Windows-off isolation; native maps/emitter intent | W0–W7 gates from the staged design, each independently qualified |

The root integrates and lands. Two independent Astra reviewers cover bootstrap and feature/bug changes. Capacity is 21 concurrent agents: root + three leads + up to five children per lead + two reviewers. Children do not recursively fan out. An idle review slot is available for the next concrete diff, not permission to repeat passing reviews. No worker owns another lane's mutable file/cache; the DB lead alone composes canonical bug DB edits.

Full agent use means concurrent independent source, regression and review work. Local memory-heavy builds are serialized through a granted slot: initial policy 48 GiB process-tree RSS, startup disk floor 26 GiB, runtime floor 20 GiB, bounded deadline. Remote native macOS CI has a separate existing workflow budget. Preserve all evidence and compatible caches; do not clear unrelated directories to make a build fit.

## Rebase and landing protocol

Fetch with the explicit refspec `refs/heads/release/1.0.0:refs/remotes/origin/release/1.0.0`; the checkout's default fetch maps only `release_phase3`. Record the fetched commit, not merely the tracking-ref name.

Rebase after a reviewable source checkpoint and before each actual build restart. Never rebase a live build or a shared dirty worktree. Preserve owned deltas and conflict evidence; do not stash or drop another lane's edits. Reconcile overlapping upstream fixes rather than replaying stale defects. Every new build freezes source/tree, producer, runtime, backend, target, cache policy and output ownership.

Astra source review and executable acceptance are distinct requirements. Zero P0/P1 findings does not turn UNRUN tests into PASS. Land only the tested/reviewed slice through a PR to `release/1.0.0`, inspect exact-head comments and change-caused failures, then merge; no direct protected push, release tag or publication. Incomplete interface work may be retained as a draft but is not completion.

## Current evidence

- PR #6373 merged the full staged design and supersession notes. It did not ship a runtime backend.
- PR #6372 merged the actual M5 checkout-reuse regression and bug DB reconciliation. Native-only macOS issues remain open/pending.
- Attempt 7: Phase 2 construction and sanity passed; full verification stopped at the disk floor; quiescence confirmed.
- Attempt 8: rebased Phase 2 binary linked, then p2_add sanity crashed. Core/disassembly identify a numeric conversion rebound to an unrelated ELF reader. A two-module pre-fix native regression also segfaults. No Phase 3 admission.
- Native macOS run 41613080079 uses frozen source ccb7f128 and the existing macos-15 Phase 2/3 workflow. Running is not passing. Inspect its actual selected job, not skipped matrix rows.
- Inventory snapshot ccb7f128: 71 platform-mentioned records, 32 open, 8 verification-pending, 18 fixed and 13 closed. Forty open/pending rows split P0=3, P1=3, P2=11, P3=23. Platform mentions include shared dependencies and historical evidence; validate relevance before assigning a repair. The new ARM64 conversion crash is an additional P0 record under registration.

## Interface and metadata decision

Use the [artifact-information design](../../../05_design/compiler/trace_artifact_information_contract_2026-11-03.md). The user's phrase “HIR optional host and MIR use with info” is awaiting semantic clarification: optional HIR for a host consumer versus optional hosted capabilities. No compiler mode or fallback changes on that ambiguous instruction alone. Preserve current legal pipeline behavior while independent repairs proceed.
