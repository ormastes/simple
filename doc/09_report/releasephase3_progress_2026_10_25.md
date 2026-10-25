# release_phase3 progress — 2026-10-25

This is an evidence update, not a fresh compiler build or acceptance run. Historical [82-scope inventory](releasephase3_coding_inventory_2026_10_25.md) and [selector reconciliation](robust_acceptance_selector_reconciliation_2026_10_25.md) are unchanged. Local `/tmp` evidence links name retained host artifacts; they are not portable repository artifacts.

Latest status: [the 13:17 UTC terminal/evidence update below](#superseding-terminal-and-evidence-update--2026-10-25-1317-utc). Earlier build observations and the 11:42 source ledger are preserved as dated history.

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
| [#4671](https://github.com/ormastes/simple/pull/4671) | `ae98d9af9c9` | Generic enum receiver source repair; generic regression specs UNRUN (canonical struct-receiver control is separate evidence). |
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

## Superseding source and acceptance ledger — 2026-10-25 11:42 UTC

This bounded update supersedes stale current-status wording above while retaining
its evidence and history. The checked target is `release_phase3` at
`a87d4fa2e3d5d0b8233ab8cd91f7b10b3d2b6ed6`. Local commit objects, relevant
worktree heads/dirty scopes and actual target symbols were inspected; no compiler,
native job, test, Hello control or whole-82-scope census was run. Local unlanded
commits below are source candidates, not portable published artifacts or PASS.

### Coded and landed at this target

| Landed source | Bounded scope; qualification remains separate |
|---|---|
| [#4815](https://github.com/ormastes/simple/pull/4815), `a87d4fa2e3d5` | Private twenty-map function-owner transport, six typed declaration-reference factories, prepaid expression reconstruction, private re-encoding and atomic install. Fixtures manually assemble snapshots/origins; they do not establish actual registration or worker provenance. Availability remains false; all new transport/runtime controls UNRUN. |
| [#4805](https://github.com/ormastes/simple/pull/4805), `4d28b903b73b` | Managed selective-worker ownership and prerequisite refusal. Requires a separately qualified cached V3 broker/image pin and delegated cgroup capability. Source does not admit current workers or prove a completed Phase3. |
| [#4808](https://github.com/ormastes/simple/pull/4808), `9b84d1514e70`; [#4772](https://github.com/ormastes/simple/pull/4772), `8388797fdf01` | Concrete lowering presence flags with reserved-bitfield correction; bounded exact decoder closure. Behavioral controls and real generator regeneration remain UNRUN. Canonical availability remains false. These newer sources are absent from the live frozen producer. |
| [#4787](https://github.com/ormastes/simple/pull/4787), `f321a4b796df`; [#4774](https://github.com/ormastes/simple/pull/4774), `874bbd5bf483` | Canonical enum capture/prepaid request verification and typed registration provenance foundations. Not complete actual-caller, full enum/composite or worker admission. |
| Equivalent landed source, `1f17a8d84a0` and `c4326166835` | Typed resolver capture/validation and prepaid scalar request-proof counts are already in the target through the combined foundation. Local original hashes `297619c5f1ee` and `2eb9285108e1` are not ancestors, but their source changes are landed. Actual caller/native integration remains OPEN. |
| [#4784](https://github.com/ormastes/simple/pull/4784), `9210d77123d0`; [#4789](https://github.com/ormastes/simple/pull/4789), `e3a710831d78`; [#4790](https://github.com/ormastes/simple/pull/4790), `15feac956b17` | Native dictionary operations13–16, typed Struct/Dictionary descriptor recipes and shared-account facades. Not operation17, text-key/rich-child/full-HIR support or complete root admission. |
| [#4767](https://github.com/ormastes/simple/pull/4767), `115ae8a9ac00` | SOURCE seals carried through final ELF protection checks. Earlier focused relocation/provider controls remain bounded history; full compiler-produced SOURCE/JIT/facade qualification is not established. |

### Coded locally but unlanded; still implementation/integration work

All following commits exist locally and are **not ancestors** of checked target
`a87d4fa2e3d5`. Active working edits are not folded into this report's owned delta.
Classification additionally checks actual source equivalence: nonancestor hashes
alone do not establish unlanded code, as the combined-foundation row above shows.

| Source candidate | What exists; what remains |
|---|---|
| Actual caller `294fccf3aaa` | A generated retained `me` caller body uses canonical Optional Some/None and Result flow. It is a WIP source candidate, not integrated caller acceptance; actual lowering/capture/verification/lifecycle closure remains incomplete. |
| Retained Optional CFG `b1c9fc84f510` | Construction verifier handles retained Optional storage/guarded borrow and authored CFG controls. Current caller lane also has tracked working edits. It is not a landed complete caller or executed native proof. |
| Verifier repair `7a9b9bc5ffc` | Rejects wrong-variant/default/shared branch targets with authored negative controls. Scoped Astra SOURCE_GO is recorded; the repair remains unlanded and runtime/integration UNRUN. Source approval adds no feature-acceptance count. |
| Stable origin `acab67c325db` | Separates stable declaration identity from later producer bodies. Reviewed candidate remains dependency-blocked and unlanded; source review is not execution. |

### Remaining selected behavior and evidence gaps

| Scope | Status at this bounded snapshot |
|---|---|
| Native operation17 | Frozen Struct-to-Dictionary write ABI exists in the [edge contract](../05_design/compiler/c4_struct_dictionary_edge_v1.md). No `rt_source_region_struct_dict_write_v1` implementation/reference exists in checked target source/tests. Assigned result-helper implementation is not a landed provider. Other dictionary operations are already coded; this is not an entirely uncoded dictionary subsystem. |
| Full graph and actual HIR root | [Integration contract](../05_design/compiler/c4_hir_region_root_integration_v1.md) remains a plan. Same-account construction before the first Dictionary/Scope birth, complete descendant/write-hook closure, authentic retained capacities and alias/staleness behavior are not complete. A post-construction graph walk/adoption cannot substitute. |
| Text keys and arrays/rich children | Current native dictionary contract is raw i64 keys with exact Struct children. Required text-key binding dictionaries, certified immutable text inputs, arrays and rich symbol/type children are not implemented/admitted by that subset. |
| Enums and Optional | Scalar/Struct and canonical enum foundations exist. The unlanded retained Optional CFG, exact owner captures and complete nested enum/composite replay/caller closure remain partial. Neither a blanket enum completion nor blanket enum absence is accurate. |
| Source admission | Component source reviews, private snapshot mechanics and descriptor seals are coded. Actual constructor/registration/worker provenance, complete graph/type support, callable/static transport and integrated SOURCE→PLAN→EMIT→artifact execution remain open. Availability is not enabled. |
| Qualified runtime and runner | The current admitted Stage2 is compiler-only. No qualified full CLI/general SSpec runner is established. All new compiler/source/transport scenarios above are UNRUN; earlier focused provider/interpreter/native controls retain only their original bounded claims. Logical accounting is not an exact native heap/RSS bound. |

### Frozen build and acceptance boundary

The coordinator reports **Phase3 attempt4 RUNNING, currently HIR**, using frozen
source `83be266ace41f453c69edf3c7f92521b5d573483` with the retained reviewed tool
lineage and admitted Stage2 SHA256
`8cd080ef9b7d59794d161beaee33c04260ca643511c58d9c19d125d6092cce1e`.
[Producer checkpoint](/tmp/phase3-next-measured-20261025/producer-only-admission-v2/stage2-producer-checkpoint.sdn)
and [compiler admission](/tmp/phase3-next-measured-20261025/producer-only-admission-v2/stage3/aarch64-unknown-linux-gnu/stage2-admitted/admission.env)
bind that producer-only boundary; matrix NOTRUN, tools UNQUALIFIED and
full_qualification=false remain explicit. Its existing Hello/receiver PASS is
not a Stage3 PASS or qualification of later landed source. This documentation
update does not poll, restart or mutate attempt4, its source, caches, runtime,
watcher or receipts. HIR progress is not an object inventory or final artifact.

The historical **82 selected feature acceptance scopes remain UNRUN**. No new
passing scenario count, full compiler/Phase3 PASS, invariant/termination proof,
formal proof, source-admission PASS, native lifetime/RSS qualification or release
readiness is added. The older 15/54/4/9 inventory is preserved as a dated census;
this scoped update does not recalculate it or certify every current row.

## Superseding terminal and evidence update — 2026-10-25 13:17 UTC

This source/docs-only update supersedes the earlier RUNNING/HIR snapshot. The
checked release target is `86e9b881c28322beb7491e66b89537892c346f87`.
Retained terminal receipts and focused native evidence were read without
rerunning their green checks, launching builds, polling peers or changing live
source/caches/locks. No fresh feature census or new acceptance count is claimed.

### Frozen compiler campaign: terminal, caches retained

| Boundary | Actual outcome and retained limitation |
|---|---|
| Attempt4 HIR/typechecking | All **1,453 modules** completed: 1,332 new plus121 cached. Typechecking completion is recorded at **4,013,907ms** (about66m54s), followed by monomorphization start. HIR completion is not object generation or a final compiler. |
| Attempt4 terminal | [Terminal receipt](/tmp/phase3-next-measured-20261025/stage3-attempt4-terminal.sdn): inner sampled cap **23,146,496KiB** (22.07421875GiB), peak **23,147,384KiB**, exit88. [Inner RSS receipt](/tmp/phase3-next-measured-20261025/stage3-attempt4-resource-cap-stop-evidence/stage3-native-build.log.rss.env) records `rss-cap-exceeded`, `quiescent=1`; this is a measured cap stop, not an inferred OOM. All **1,453 HIR and1,453 frontend entries** remain preserved. |
| Attempt5 | [Retained exit status](/tmp/phase3-next-measured-20261025/stage3-resume-attempt5-exit.code) is64; refusal occurred in Stage2 verification **before compilation**. The changed source/git/tool state no longer matches the admitted interval. Fresh preflight does not replace those exact comparisons or authenticate new inputs. |
| Producer v3 remint | **Never launched.** The finite900-second wait for an external heavy process ended124, with no extension; [wait exit status](/tmp/phase3-next-measured-20261025/producer-remint-v3-peer-wait-exit.code). No new producer/compiler admission exists from this attempt. No peer paths or private command lines are included here. |
| Remaining attempt budget | Final Stage3 attempt6 is **unspent**. Conditional resource design is reviewed; fresh producer and actual launch admission remain pending. No proposed future cap is a qualified fit. It is not an already-running, scheduled-success or admitted result. Root retains launch/resource ownership. |

The existing canonical resume verifier compares admitted source, Git and tool
snapshots independently (the attempt5 owner retains the checks at
`resume-stage3-from-admitted.sh:666–678`). The supported recovery is a **real fresh
canonical Stage2 producer/checkpoint** over the intended immutable inputs, with
its actual sanity, receiver, runtime, tool, planner and admission evidence.
Do not rewrite old snapshots, forge stamps, substitute a preflight receipt or
reinterpret the producer-only checkpoint as full tool qualification. Compatible
cache entries remain subject to the existing lineage checks.

### Newly landed source and focused evidence

| Landed change | Evidence boundary |
|---|---|
| [#4828](https://github.com/ormastes/simple/pull/4828), `13c94b195634` | Explicit Stage3 RSS-cap transport is pinned across controller, worker, transcript, invocation hash and child budget/watchdog. Its actual shell fixture passed and Astra reviewed the source; this does not turn attempt5's changed admission inputs into valid ones or establish a new compiler PASS. |
| [#4832](https://github.com/ormastes/simple/pull/4832), `d9dc34a62246` | Canonical enum duplicate-map work/capacity is prepaid before growth. Scoped SOURCE_GO; executable compiler scenarios remain **UNRUN**. No runtime or full enum/caller acceptance follows from source review. |
| [#4834](https://github.com/ormastes/simple/pull/4834), `86e9b881c283` | **Proposal/documentation only:** authentic immutable text birth/lifetime contract. Not implemented text-key/full-HIR admission or a runtime-qualified text provider. |
| [#4823](https://github.com/ormastes/simple/pull/4823), `79f07910a691` | Native Struct-to-Dictionary operation17 is coded and landed. This supersedes its absence in the older11:42 target. Actual C4 invocation, compiler emission/planning, whole-graph behavior and all selected acceptance remain separate. |

The **one retained operation17 native fixture** used source
`9d4dcb77aebac52f88fb8638d701c3bb47241545`, after operation17 landed.
[Source pin](/tmp/op17-native-evidence-20261025/source-revision.txt),
[recorded run](/tmp/op17-native-evidence-20261025/run.sh),
[stdout](/tmp/op17-native-evidence-20261025/stdout.log) and
[exit code](/tmp/op17-native-evidence-20261025/exit.code) record ASan/UBSan,
`op17 native fixture PASS`, and exit0. The binary's independently read SHA256 is
`466a6d034c71e1174c4a956832907b169cca015dcf90d6b6253616448659e70f`.
The [RSS receipt](/tmp/op17-native-evidence-20261025/rss.receipt) records
peak **233,764KiB**, `quiescent=1`, and **hard_memory_limit=0**: sampled accounting,
not a hard-memory enforcement guarantee. This focused provider PASS was not
rerun and is **not** a compiler/HIR/SOURCE admission, general runner qualification,
whole-graph proof or PASS for any of the82 selected acceptance scopes.

### Full goal and required end conditions remain unchanged

1. Produce the real fresh canonical Stage2 compiler for the intended frozen
   source/tool/runtime lineage; require its actual sanity/Hello, receiver,
   planner and producer-admission/checkpoint evidence without weakening gates.
2. Use it to finish the Phase3 compiler, then have that exact compiler compile
   Hello and execute its output correctly. No Phase3 compiler binary or its own
   Hello PASS exists yet.
3. Complete the required next compiler generation with genuine lineage and
   executable qualification; a focused provider fixture cannot replace it.
4. Build and qualify the full CLI and existing general SSpec runner, then run
   every selected acceptance scope with actual registered/executed assertions.
   All **82 feature acceptance scopes remain UNRUN**; no loading-only result,
   missing runner or zero-case run counts as PASS.
5. Complete remaining actual C4 caller/invocation and lifecycle integration,
   full reachable graph/constructor/write closure, text keys/immutable text,
   arrays/rich children and exact enum/Optional replay, source admission and
   required backend/runtime/native evidence. Preserve ordinary behavior and
   independent review; logical budgets and isolated provider results do not
   establish complete heap/RSS, proof, source authority or release readiness.

Older source-candidate and implementation classifications above retain their
own pins and dates; this update neither recertifies every row nor narrows the
selected robust goal. There is still no full Phase3 PASS or qualified CLI/runner.
