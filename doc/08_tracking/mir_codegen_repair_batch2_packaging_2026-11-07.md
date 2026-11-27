# MIR/codegen repair batch 2: packaging inventory

Status: reviewed source repairs landed; Boolean generated artifacts and compiler/runtime qualification remain pending. No all-bugs-complete or runtime PASS claim.

## Observed integration snapshot

- Target: `release/1.0.0`.
- Observed 2026-11-07 02:10:01 UTC: commit `3362849eda19d05b6e9b4a3aa0782681da2e2471`, tree `86f0b3ddc11d4d2120a453012685c6d3b9a0c13a`.
- Source workspace: `D:/dev/simple-node-attribute-20261106`, local HEAD `991d28d8cca496baf603c4779d621293fc123448`. Local dirty/staged files include previous landed work and independent in-progress work; they are not a package manifest.
- Previous scoped PRs #7437, #7434, #7440, #7443 and #7448 are merged and their owned temporary remote branches were deleted. Their source-only approvals do not qualify this batch or establish runtime verification.

## Lane inventory

The rows below record requested investigation areas. A row is not evidence that a bug has been reproduced or fixed. Rows without final admission still require owned paths, tests and review receipts.

| Area | Owner / reviewer | Packaging evidence | Runtime evidence |
|---|---|---|---|
| Boolean binding codec/generated hash propagation | Sol Bool / Astra Node | Twelve-path candidate includes shared `mir_lowering_stmts`, generator/codec/HIR/semantics sources, codec/transform/provenance tests, fixture and a native runner; generated codec/hash remain stale, so publication is blocked | Native runner authored for two backends with ten checks each; unexecuted |
| MIR Result Err lowering and CLI shortcut | Sol MIR / Astra MIR | Combined final source/tests/reports approved and merged with closure lane; preserves concurrent Err empty-owner fallback. Historical invalid-heap attribution remains open | Tests/fixtures unexecuted |
| Cranelift code generation | Sol Cranelift / Astra Cranelift | Final five-path source scope approved and merged: integer power, floating remainder and actual destination shift masking | Typed-MIR/JIT 66 cases and native 33-case fixture authored, unexecuted |
| LLVM code generation | Sol LLVM / Astra LLVM | Combined LLVM/memory final source and reports approved and merged; nine call-ABI scenarios authored | Tests unexecuted |
| SVM-G lowering | Sol SVMG / Astra SVMG | Source/spec/report approved and merged: staged call arguments, zero-word helper return rejection, positive signed-step wrap exit; seven new parameterized tests | Tests unexecuted |
| Native ABI | Sol Native ABI / Astra Linker | Four-path integer stack-argument repair approved and merged; eight selector cases and four fixture assertions | Tests/fixture unexecuted |
| Phi/control-flow joins and compound assignment | Sol Phi / Astra Phi | Isolated 17-line merge repair approved and merged with seven tests; separate five-addition/one-deletion mapping repair approved and merged with ten HIR scenarios | Tests unexecuted |
| Closures | Sol Closure / Astra Closure | Shared source and six slot-matrix scenarios approved and merged with MIR lane | Tests/fixture unexecuted |
| Memory operations | Sol Memory / Astra Memory | Combined LLVM/memory shared source approved and merged after chained-GEP metadata corrections; eleven scenarios authored | Tests unexecuted |

Canonical bootstrap execution and admission belong to the separate bootstrap owner. Packaging did not execute a compiler or generator and claims no compiler/bootstrap admission. Historical attempt-12 observations are independent evidence, not qualification of these newer source repairs.

For post-admission generator preparation, a separate frozen source snapshot was created at `D:/dev/simple-schema-generator-source-20261107-9abc963a`, based on release commit `9abc963a05802c33fa558c2930797b950caa1c56`, tree `0fb7a513f90bbd427cf03c445f38f3949753f27d`. Its `generator-source-overlay.sdn` SHA-256 is `93B5C3F015DF57BED213D4DC3CB6322623883CCE58667B2AD63BDAF57BA4FBCE`. The Boolean owner accepted the seven scoped input overlays, updated visitor/HirStmt inputs and unchanged generated-file guards by read-only inspection. No compiler or generator was executed for this preparation; the generated-artifact publication blocker remains. This snapshot must remain unchanged during consumption, including when release advances.

At initial packaging, the observed release commit could not be resolved in the source workspace's local object database. GitHub confirmed `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` existed at that historical snapshot with blob `1498e758e37171ee6aeac51d38854816a62d6afa`; the local `git show` failure did not establish a rename or missing file.

Confirmed existing owner blobs at the observed release snapshot:

| Source owner | Blob |
|---|---|
| `src/compiler/70.backend/svmg_lowering.spl` | `0b01543a132b10e49c6e79e074a7d5580f634cc5` |
| `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` | `6b42a6b4409ac91130b94edf369084d46acb42dc` |
| `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl` | `0716f9ae50ded1c5e8bd7b392fdcf83906045b41` |
| `src/compiler/70.backend/backend/native/isel_x86_64.spl` | `e8651602d66d098b01c7031ef8a5ecf06890a989` |

## Reviewed source landings

All seven entries are merged, with source-only approvals and compiler/native tests unexecuted. Root reviewed the final heads, comments and applicable CI; these checks do not establish runtime qualification.

| PR | Approved scope | Final head |
|---|---|---|
| #7460 | SVM-G source/spec/report; seven new parameterized cases | `4cda90f8c4283ea9e2a3e963866b1ffef678c615` |
| #7461 | Native x86 integer stack-argument source/spec/fixture/report; eight selector cases | `e310b75cdf54e82f42d3142f276bd5f29f51f594` |
| #7463 | Isolated phi source 17 additions and seven-case spec; Boolean and assignment-mapping hunks excluded | `10ae05cbedfdb90ec7957cb04ba6bba11f22729c` |
| #7465 | Combined LLVM call/memory three sources, two specs and two reports | `f67fba908a5cab3235ab75a482f3f8e6508f118d` |
| #7466 | Isolated exhaustive compound assignment mapping and ten-case HIR spec; Phi preserved, Boolean excluded | `0013c51b9d202ae8c17070b48405c32141b5c20b` |
| #7467 | Combined MIR Result/CLI/closure two sources, three specs, three fixtures and three reports | `b61d09626f0c872f0f7bbb6c74283fd39b0ee6cc` |
| #7468 | Cranelift adapter, typed-MIR shift spec, integration runner, power/remainder fixture and report | `937bd53d86abf2428966020735e97be4fd50d86b` |

The initial phi raw artifact used CRLF throughout against the release LF source, inflating the remote diff. The unmerged branch was replaced under an exact-head lease after Astra approved the canonical LF artifact. The final remote comparison shows exactly 17 source additions and zero source deletions; the noisy initial candidate is not the PR head.

Confirmed merges: #7460 `31659d3f2ca0dbcde9e4e38bfaa9771e337ecf2e`; #7461 `140a26bb5a0bbcdf4a68d952527362be9e091552`; #7463 `4eb1de2ecbdb286b539e1d7f76e8e47ff4fcced1`; #7465 `75e6c978808b1083878d092b5b40fa17f3fee8e7`; #7466 `99f9426821d6b12e5771d921619097afec470d4e`; #7467 `a7a25ad8070c9abec75d9f8ad10bdb1b1a3ec092`; #7468 `f213d2db3e592f63291dcb037e88ea045deb3810`. All seven owned temporary remote refs were deleted after merged-head/ref checks; local feature branches and unrelated files were preserved.

The separate five-path host-lock prerequisite repair #7509 is also merged: approved head `e08fac22acf32b574c3860a68013ab57858c3aee`, merge `4d0fe17db52a3f998eddeeb76833c178a7258614`. Its owned temporary ref was deleted after exact merged-head/ref checks. Retained Windows logs show six focused observer assertions and the two-case stale-owner selftest passing. Earlier baseline/expanded logs survive only in the session transcript after ignored logs were lost; no reconstructed logs or final all-group rerun are claimed. Linux qualification was unavailable because WSL's configured VHDX and Docker's Linux engine were absent. Unpatched peers still require quiescence or a coordinated compatible runtime arrangement; this host evidence does not admit a compiler or bootstrap.

## Shared-owner integration

- LLVM and memory repairs share `core_codegen.spl` and `aggregate_intrinsics.spl`; both Astra reviewers approved the combined final diff in #7465.
- MIR ResultErr/CLI and closure repairs share `switch_operators_calls.spl`. Packaging detected a concurrent release change from owner `1498e758e37171ee6aeac51d38854816a62d6afa` to `28e56b910b6945880d9f0fb8795239e527eb8765`. Sol integrated the already-landed Err empty-owner fallback, and both Astra reviewers approved final SHA-256 `144073B5A2AE2E7DE5C4796BA003111B153965DA74D848B82A11049298F5005B` before #7467 was created.
- Phi and compound assignment share `mir_lowering_stmts.spl` with the unlanded Boolean binding hunk. Their isolated candidates were integrated onto the release owner and reviewed separately; Boolean changes remain excluded while generated artifacts are stale.

## Packaging admission

Each package needs an explicit owned-path list, authored reproducing/prevention tests, and Astra approval of the final source/test/report scope. Static inspection, arithmetic oracles, authored tests, compiler execution and native execution are recorded separately; unexecuted tests remain marked unexecuted.

Before creating a candidate tree, refresh the target release commit and compare every existing owned-path blob with the lane's starting owner blob. Preserve concurrent changes; a differing owner requires integration and renewed final review. Shared source files require root serialization rather than whole-file replacement. Candidate trees contain only the approved owned paths and use the refreshed release tree as their base.

Packaging may create isolated `work/*` PRs after admission. Root owns exact-head review and merge. No direct protected-ref updates, release tags, broad commits, unrelated staged changes, or pending source work are admitted by this inventory.

Global bug-claim reap prerequisites are satisfied centrally. Lane agents were instructed not to repeat global reaping or write the bug database. Existing operational database changes are preserved and excluded from every package.
