# release_phase3 progress — 2026-10-25

This is an evidence update, not a fresh compiler build or acceptance run. Historical [82-scope inventory](releasephase3_coding_inventory_2026_10_25.md) and [selector reconciliation](robust_acceptance_selector_reconciliation_2026_10_25.md) are unchanged. Local `/tmp` evidence links name retained host artifacts; they are not portable repository artifacts.

## Current update — 2026-10-25, after PR #4657

GitHub confirms [PR #4657](https://github.com/ormastes/simple/pull/4657) merged at **c345d0a6e589a40c237d0dbe97899bae7c89da17** (04:59:54 UTC). The bounded dictionary scope-read providers and five interpreter wrappers are landed with source review GO. This adds real scalar reads through existing native C, pure Simple and hosted Rust owners, with owner/epoch/backing/fuel checks; it does not add the pending HIR constructor account or complete SOURCE integration.

| Newly recorded boundary | Evidence and limitation |
|---|---|
| Actual interpreter dispatch | [Retained test log](/tmp/c4-scope-read-interpreter-cycle6-20261025.log): **3 passed,0 failed**, through registered handlers; raw-handle order/UTF-8/wide IDs, stale/invalid/fuel refusal, rich-dictionary refusal and arity controls. No tests rerun for this report. |
| Hosted runtime scope reads | Prior **8 focused runtime tests passed**; see [admission-index overhead record](../08_tracking/bug/c4_hosted_scope_read_admission_index_overhead_2026-10-25.md). The extra lifecycle admission index has allocation/mutation cost even without queries; whole-compiler overhead remains unmeasured. |
| Native provider | [Executed native controls](../08_tracking/bug/c4_scope_read_runtime_qualification_2026_10_25.md):2,049 bindings,300,000 reads,zero read allocations,12.7ms and isolated maximum RSS 1,616KiB. This is the isolated reader, not a full-compiler performance result. |
| Pure runtime and typed facade | Array/numeric/memory objects compiled. Full pure runtime execution remains blocked by reproduced baseline string HIR failures; the typed facade/account closure reached HIR but crashed in MIR. Typed facade execution, actual SOURCE queries, physical storage accounting and whole-compiler performance remain **OPEN**. |

These bounded runtime/dispatch results do not change the full **82-scope feature acceptance matrix: all UNRUN**. The carried inventory remains 15 complete-unverified/54 partial/4 absent selected behaviors/9 authority decisions; this update does not re-audit every row or mark an entire scope complete. The static 33, C4 foundation 37 and builder 20 SSpecs below remain UNRUN.

### New compiler snapshot, still awaiting matrix result

Source **89d2e18cd1487a1f3c5b2c248f9096b3df6b4b0a** (including the persistent-root runtime fix) rebuilt **1,496 modules,0 reused,0 failed**, and linked candidate **95c332194465d5ea2a126687c4152168cb59d7c2be0e48bde53e168966476c1f**. [Build log](/tmp/phase3-stage2fix-89d2/canonical-admission/logs/aarch64-unknown-linux-gnu/stage2-native-build.log); [focused admission receipt](/tmp/phase3-stage2fix-89d2/canonical-admission/stage3/aarch64-unknown-linux-gnu/stage2-admitted/admission.env). The receipt binds source snapshot 3196f166… and runtime snapshot 52bd28a4…. This older source does not qualify the newer c345d0 scope-read code.

[Planner admission](/tmp/phase3-stage2fix-89d2/canonical-admission/stage3-planner-admission.receipt) is pass. Its [negative control](/tmp/phase3-stage2fix-89d2/canonical-admission/admission/d2d412f8f9c1a62f69f6b2decb438e0c4a10fbd53f98b29f946f6d53f1d7951a/planner-smoke.txt) rejects an untyped reason with exit 2 and writes no receipt; the [authorized control](/tmp/phase3-stage2fix-89d2/canonical-admission/admission/d2d412f8f9c1a62f69f6b2decb438e0c4a10fbd53f98b29f946f6d53f1d7951a/planner-stdout.txt) records the selected reason and execution=not-attempted. These are planner controls, not completed Stage3 execution.

The [compiler test matrix summary](/tmp/phase3-stage2fix-89d2/canonical-admission/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/summary.env) is still being written at this snapshot; no terminal matrix PASS/FAIL or new full CLI/runner qualification is claimed. The requested 500-item cached batch is not yet recorded as executed.

### Older provisional campaign: terminal watchdog refusal

The older ce7738/f5c0 campaign is now terminal: [watchdog receipt](/tmp/phase3-provisional-stage3-ce7738-f5c0-20261025/tmp/simple-process-tree-rss.614077.env) reports **rss-measurement-failed,exit 89,quiescent=1**. The [retained log](/tmp/phase3-provisional-stage3-ce7738-f5c0-20261025/stage3-diagnostic.log) last records **HIR 960/1,441**; no final compiler binary was produced. The earlier 942 observation below is preserved as an earlier progress point, not a unique-object inventory. The terminal helper observation took about 2,095.6ms; session_helper_integrity=verified. This timing does **not** establish a SHA/hash root cause, an OOM, or a compiler pass. It is separate from the newer source 1690 SIG11 record below.

## Landing update — 2026-10-25 04:31 UTC

[Runtime repair PR #4641](https://github.com/ormastes/simple/pull/4641) is now **MERGED** at `89d2e18cd1487a1f3c5b2c248f9096b3df6b4b0a`, following independent Astra source review. Its production/test code matches the reviewed `8e535e297367e2fec0c332af9b52067a9fce3d95` repair. The retained 22 runtime unit passes and expected negative-control failure below remain the same evidence; they were not rerun. Accumulated-root quadratic growth remains performance debt, and the original compiler graph on a rebuilt matching runtime remains **UNRUN**. All 82 feature acceptance scopes remain UNRUN; the 500-item cached batch remains requested, not executed. The 75d260 GitHub snapshot and then-pending runtime review below are preserved as dated history.

The retained core analysis links below identify the inspected failure. The extracted CoreDump was subsequently removed after a duplicate-hash check; the original apport path was later rewritten by another crash. Core-file recovery is uncertain; this report claims only the retained stack/owner/disassembly observations, not current availability of the original core.

## GitHub snapshot and implementation

Fresh `git ls-remote` and GitHub PR queries observed `release_phase3` at **75d260930c3b16af91c79d4fc860cf6749e2000d**, and `release/1.0.0` at **7c761b605398b4c401c85914581f57c6179fe03c**. No open PR targeting release_phase3 appeared in the query; the latest 15 listed PRs were merged. This does not assert anything about other branches or every repository PR.

| Merged PR | Landed scope |
|---|---|
| [#4556](https://github.com/ormastes/simple/pull/4556) | VMM static exports used across modules |
| [#4563](https://github.com/ormastes/simple/pull/4563) | Acceptance selector reconciliation |
| [#4578](https://github.com/ormastes/simple/pull/4578) | Reverse-reference ownership across module teardown |
| [#4586](https://github.com/ormastes/simple/pull/4586) | Enum carrier preservation and optional environment restoration |
| [#4599](https://github.com/ormastes/simple/pull/4599) | Source-backed82-scope coding inventory |
| [#4605](https://github.com/ormastes/simple/pull/4605) | Bounded static lock-level checker |
| [#4606](https://github.com/ormastes/simple/pull/4606) | Stop idle shard replacement generations |
| [#4607](https://github.com/ormastes/simple/pull/4607) | Unwrap optional fold edges before typed traversal |
| [#4609](https://github.com/ormastes/simple/pull/4609) | Reflect static checker in the coding inventory |
| [#4612](https://github.com/ormastes/simple/pull/4612) | Remove unused HIR declaration-owner map construction |
| [#4618](https://github.com/ormastes/simple/pull/4618) | C4 account/provider foundation |
| [#4627](https://github.com/ormastes/simple/pull/4627) | Actual MirBuilder scalar construction hooks |

The last full inventory remains **15 coded-complete but unverified,54 partial,4 absent selected behaviors,9 requiring authority/requirement decisions =82**. Later C4 foundation/hook landings improve components but do not close full selected physical accounting or general loop verification. These counts are carried forward, not a new82-row audit. Partial means selected behaviors remain; it does not mean an entire subsystem is uncoded. All 82 selected feature acceptance scopes remain **UNRUN**.

| Newly landed test surface | Authored scenarios | Execution | Remaining scope |
|---|---:|---|---|
| [Static lock-level SSpec](../../test/03_system/app/compiler/feature/static_lock_level_spec.spl) |33|UNRUN|Broader alias/manual-guard/async cases and native qualification; [bounded implementation report](static_lock_level_2026-10-25.md) |
| [C4 account/provider test plan](../03_plan/sys_test/c4_account_provider_foundation_v1.md) |37 (7+21+9)|UNRUN|Authentic physical capacity/copy handoffs and full SOURCE→PLAN→EMIT composition |
| [Actual builder capture SSpec](../../test/01_unit/compiler/mir/loop_view_builder_capture_v1_spec.spl) |20|UNRUN|Parsed SOURCE authority, complete constructor/replacement/metadata coverage and source sealing; [authored manual](../06_spec/01_unit/compiler/mir/loop_view_builder_capture_v1_spec.md) |

Scenario counts are authored tests, not pass counts, and must not be added to the historical 378 manifest selections without reconciliation. The preserved selector inventory names 231 unique paths (211 present and 20 open selectors); neither that inventory nor the historical 378 selections certifies execution.

## Build and admission receipts

| Boundary | Recorded outcome | Exact retained evidence |
|---|---|---|
| Stage2 build, source 1690b09c34dd45df444d95bb02eeda568dd9f0b0 |1,492 rebuilt; build completed|[build log](/tmp/phase3-stage3fix-1690/canonical-admission/build.log), [command transcript](/tmp/phase3-stage3fix-1690/canonical-admission/stage3/aarch64-unknown-linux-gnu/stage2-command.transcript) |
| Stage2 frontend smoke, SIMPLE_BOOTSTRAP=0 and1 |Both raw statuses0; sanity status pass|[sanity receipt](/tmp/phase3-stage3fix-1690/canonical-admission/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env) |
| Struct receiver and positional Stage3 route |pass; candidate and runtime identities stable|[receiver receipt](/tmp/phase3-stage3fix-1690/canonical-admission/stage3/aarch64-unknown-linux-gnu/stage2-receiver.env) |
| Focused Stage2 admission |admitted candidate7934d8c2e119a56098c49c0d996c52070eb962e156ce3855a723d29824cbf550|[admission.env](/tmp/phase3-stage3fix-1690/canonical-admission/stage3/aarch64-unknown-linux-gnu/stage2-admitted/admission.env) |
| Stage2 compiler test matrix |FAIL; full CLI build failed, no qualified CLI from this matrix|[summary.env](/tmp/phase3-stage3fix-1690/canonical-admission/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/summary.env), [CLI log](/tmp/phase3-stage3fix-1690/canonical-admission/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/compiler_cli_build.log) |
| Provisional Stage3 from7934/source 1690 |exit117; driver SIGSEGV during HIR; no final compiler artifact|[watchdog receipt](/tmp/phase3-stage3fix-1690/provisional-stage3-1690-diag2/watchdog.env), [build log](/tmp/phase3-stage3fix-1690/provisional-stage3-1690-diag2/logs/build.log), [identity](/tmp/phase3-stage3fix-1690/provisional-stage3-1690-diag2/identity.env), [ordinary core stack](/tmp/phase3-stage3-1690-core-review/stack.log) |

The admission receipt binds source snapshot `d39bac84ca31055c7bf364cbb9ebefdb8177da07b076516ef5c2c207a0f65bf0`, runtime snapshot `fde41655eea6ba5bc99b14e66ff0f030a866cf49aca403713dada7cf000a7dd1` and hosted runtime `c04ddb79332fbd2219504c820c30295bf1304724a13cbe0fe0c5cd6207c1845d`. It admits the focused source 1690 producer boundary; it does not qualify current 75d260, the failed compiler matrix, the full CLI or full Phase3.

The first located CLI error is `conflicting physical source` for `std.cli.log_modes`, source index3, in the immutable b2e5c6cf… SCV snapshot. The preceding physical file was parsed and committed at index2. [Bounded diagnosis handoff](/tmp/phase3-scv-alias-debug-20261025/diagnosis-handoff.md) confirms the rejection but does not prove whether path, length or hash mismatched. Six diagnostic/setup attempts were retained; no blind donor port or conflict suppression was applied.

The provisional core terminates in `surface_decl_owner_indices`; the watchdog reports peak 6,383,848KiB. [Owner-array observations](/tmp/phase3-stage3-1690-core-review/owner-array-state.log) and [promotion disassembly](/tmp/phase3-stage3-1690-core-review/promote-disassembly.txt) support the ongoing runtime ownership investigation. A measured peak is not evidence that the crash was an OOM.

## Pending runtime repair and continuation

At the GitHub snapshot recorded at 2026-10-25 04:23 UTC, runtime repair **8e535e297367e2fec0c332af9b52067a9fce3d95** is under independent review, **not landed**; see its [source bug record](/tmp/simple-phase3-persistent-root-promotion-20261025/doc/08_tracking/bug/releasephase3_persistent_root_promotion_2026_10_25.md). Retained [evidence.sdn](/tmp/phase3-persistent-root-evidence-20261025/evidence.sdn) explicitly says production_authority_admitted=false. [Fixed Rust runtime unit tests](/tmp/phase3-persistent-root-evidence-20261025/fixed-tests2.log) report22 passed; the [negative control](/tmp/phase3-persistent-root-evidence-20261025/negative-tests.log) fails its intended assertion. These are runtime-unit results, not executed Simple feature SSpecs or a rebuilt/admitted compiler.

The [accumulated-root benchmark](/tmp/phase3-persistent-root-evidence-20261025/benchmark-runtime.log) reports9.34→34.11→127.63ms for64→128→256 rounds of 64 children (4,096→8,192→16,384 final children), peak 7,072KiB in the evidence receipt. Growth is approximately quadratic for this accumulated graph workload; do not label it linear, a performance fix, or a full compiler RSS result. Production runtime/provider rebuild, exact crash reproduction and source-matched compiler qualification remain pending.

The [older stalled diagnostic log](/tmp/phase3-provisional-stage3-ce7738-f5c0-20261025/stage3-diagnostic.log) contains progress count 942, **not a verified count of unique object artifacts**; it cannot establish remaining link inputs. The requested cache-backed500-item batch is **REQUESTED, NOT EXECUTED**, waiting for the reviewed runtime repair and an admitted matching producer. Do not restart the failed full bootstrap or count cache entries as admitted objects.

## Completion conditions

1. Review and qualify the runtime repair against the exact producer/provider and preserved failure; retain negative controls and honest performance limits.
2. Resolve the SCV alias conflict without suppressing genuine conflicting contents, then build and admit the ordinary full CLI and existing test runner with the selected phase compiler.
3. Resume compatible cached object work under matching source/runtime fingerprints, finish all required modules, link the complete Phase3 compiler, and have that exact compiler compile and run Hello World.
4. Execute the selected acceptance matrix with the existing runner; record actual executed/pass/fail/skip counts and source/runtime identities. Only accepted receipts can change UNRUN or close the selected requirements. No new test toolchain or inferred PASS from merged code.

No release tag/publication, full Phase3 PASS, current-head acceptance PASS or final feature-completion claim is made by this update.


## Annotated continuation — 2026-10-25, through PR #4728

This append records a later bounded snapshot; the preceding failed and pending reports remain historical evidence. GitHub merged-state inspection confirmed all ten PRs below, through release head `0731c69ea8fcf9f589edee22b0f37b06cf810fb4`. No fresh 82-scope audit or feature acceptance run was performed. The historical inventory remains 15 complete-unverified / 54 partial / 4 absent selected behaviors / 9 authority decisions = 82, with full acceptance of all 82 scopes UNRUN. Authored specs and source GO are not executed PASS counts.

| Merged PR | Scoped source head | Result and qualification limit |
|---|---|---|
| [#4671](https://github.com/ormastes/simple/pull/4671) | `ae98d9af9c9` | Generic enum receiver source repair; focused frozen-candidate receiver control passed, broader feature acceptance UNRUN. |
| [#4674](https://github.com/ormastes/simple/pull/4674) | `8901574c710` | MMIO owner/test-mode repair; source review GO, authored feature specs UNRUN. |
| [#4675](https://github.com/ormastes/simple/pull/4675) | `29e3fbd72cc` | CUDA no-guess layout source repair; runtime/PTX execution UNRUN, portable-type acceptance OPEN. |
| [#4680](https://github.com/ormastes/simple/pull/4680) | `ae0006adbc6` | Root semantic Markdown lint dispatch; source GO, runtime/docgen acceptance UNRUN. |
| [#4712](https://github.com/ormastes/simple/pull/4712) | `5fe28b79e77` | Exact pinned reviewed transient exceptions coded; source GO, authored root/doc controls UNRUN. |
| [#4717](https://github.com/ormastes/simple/pull/4717) | `715ad78fd5f` | LLVM descriptor source integration; full SOURCE execution OPEN. |
| [#4722](https://github.com/ormastes/simple/pull/4722) | `89fd8c288b2` | Cranelift bridge: actual AOT readonly relocation/RELRO controls PASS; JIT/facade execution UNRUN. |
| [#4725](https://github.com/ormastes/simple/pull/4725) | `bae38b2d10b` | Scalar Result helpers; preservation source GO, compiler specs UNRUN. |
| [#4727](https://github.com/ormastes/simple/pull/4727) | `02d0bcd3d47` | Scoped scalar SOURCE integration; exact preservation source GO, executable acceptance UNRUN. |
| [#4728](https://github.com/ormastes/simple/pull/4728) | `91bccabbb26` | Active native provider and standalone ASan/UBSan controls PASS; merge `0731c69ea8f`, full SOURCE acceptance OPEN. |

Native provider verification used six attempts in total and preserved the ordinary 16-byte allocation-registry entry. It establishes focused active-provider and standalone sanitizer behavior, not full compiler-produced SOURCE execution. Generic per-function owner replay, actual request/context lifetime and cleanup, final ELF-span protection, remaining roots/container transports, pure/hosted parity and performance remain OPEN. Cranelift AOT relocation/RELRO results do not qualify JIT or facade execution.

### Frozen Stage2 continuation and retained receipts

Frozen source `46772223a7c39ddd50a4f8198c6c4724f40ab444` rebuilt 1,497 objects, 0 failed, in approximately 269 seconds, producing candidate SHA256 `991be8f97493426d22fa944bd212afa22487bb22b31d2a6ea0ab95e8b4e05974`. The first frontend mode-1 control timed out under contention; the instrumented mode-1 diagnostic passed. Canonical cycle 3 reused 1,495 objects and rebuilt 2, yielding the identical candidate. See [build log](/tmp/phase3-resume-20261025-4674/cycle3-build.log), [timeout diagnosis](/tmp/phase3-resume-20261025-4674/admission-timeout-diagnosis.sdn) and [actual product budget](/tmp/phase3-resume-20261025-4674/cycle3-actual-product-budget.env). The budget reports sequential HIR fallback (`HIR threads 0`) and backend argv 10; configured concurrency is not proof of parallel execution.

The [focused Stage2 admission](/tmp/phase3-resume-20261025-4674/canonical-admission/stage3/aarch64-unknown-linux-gnu/stage2-admitted/admission.env) is admitted and [sanity receipt](/tmp/phase3-resume-20261025-4674/canonical-admission/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env) passes. Both [frontend mode 0](/tmp/phase3-resume-20261025-4674/canonical-admission/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-bootstrap-0.status.env) and [frontend mode 1](/tmp/phase3-resume-20261025-4674/canonical-admission/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-bootstrap-1.status.env) record Hello positional raw status 0; the canonical owner requires exit 0 and Hello stdout before recording PASS. Full-profile stdout is not retained separately. Receiver and planner controls also passed. These are candidate-bound controls, not acceptance of newer live source.

The latest coordinator watcher observation was HIR 814/2,914, succeeded 814, failed 0, elapsed 1,120,664ms in the [running compiler CLI build log](/tmp/phase3-resume-20261025-4674/canonical-admission/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/compiler_cli_build.log). This is a nonterminal snapshot: MATRIX RUNNING, full CLI not yet qualified. Stage3 has NOT STARTED. The requested cache-backed 500-item batch is NOT YET EXECUTED. No new build, test launch or whole-feature audit was performed for this documentation append; full Phase3 remains incomplete.
