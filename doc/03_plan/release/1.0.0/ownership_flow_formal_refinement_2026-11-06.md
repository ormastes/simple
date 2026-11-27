# Ownership-flow model and refinement admission

2026-11-06; release lane baseline `77b05b3a4fb6a3cb3c5b92c2b74cea56b4799b74`. This retains a focused historical **MODEL_PROVEN** result, with surviving traces described below, contributing to FV-OWN-02, not closure of FV-OWN-02 or any other full memory-plan obligation. The production Simple twin is **NOT_RUN** pending an admitted runtime. All 12 full FV obligations remain open.

## Exact model

`src/verification/ownership_flow/src/OwnershipFlow.lean` models production `OwnershipEvent.Read`, `Move`, `Write`, `Revive` and maybe-moved state lists. Places retain Local/Static/Promoted base identity and Deref/Field/Index/ConstantIndex/Downcast projections. Numeric identity uses `BitVec 64`, preserving equality for the Simple `i64` bit domain; the model performs no arithmetic on IDs. Source bytes and exact declaration hashes are recorded in `source_bindings.sdn`.

The model reproduces `place_elem_may_overlap`: different symbolic index locals may select the same element; symbolic and constant indices may overlap; distinct constant indices and distinct field IDs do not. Overlap follows the shorter matching projection prefix. Revival requires exact prefix coverage and refuses any symbolic index in the write prefix, even if the symbolic local ID matches. A whole-local write can revive its moved descendants; a field write cannot revive an ancestor move.

Move adds a place only if absent, Read and Write preserve facts, Revive filters only definitely covered facts. Write rejects access through a moved strict ancestor but permits replacing the exact moved target; the adapter follows accepted Write with Revive. Successor merge inserts missing facts and preserves hazards from either reachable predecessor; terminal predecessors contribute nothing. These facts model the solver's set semantics without discarding its actual place structure. They do not prove worklist convergence, loop analysis, borrow effects, runtime memory allocation or unique rooted heap ownership.

## HIR/source relation

| Production owner | Model relation | Remaining obligation |
|---|---|---|
| `borrow_graph.spl` PlaceBase/PlaceElem/Place and overlap/equality functions | Base/Elem/Place and conflicts/coversPath preserve all declared cases | Execute production twin and independently review the source binding; no automatic compiled equivalence is claimed |
| `ownership_flow.spl::ownership_event_transfer` and `ownership_write_covers` | transfer/covers implement same generation/kill membership rules | Actual compiler/runtime array/value semantics and allocation failures remain outside the pure model |
| `OwnershipFlow.check` successor merge and diagnostic replay | merge membership and rejecting Read/Move on overlapping maybe-moved place | Full reachable fixed-point soundness, order independence beyond membership, budget accounting and malformed CFG behavior require the real solver corpus |
| `hir_ownership_facts.spl::hir_ownership_read_v1` | Accepted resolved non-short ownership transfer emits Read then Move; non-transfer read emits Read | New HIR extraction is still under implementation; its whole-source hash is deliberately not frozen as an admitted binding here |
| `hir_ownership_cfg.spl::hir_ownership_branch_v1` | Only nonterminal branch exits connect to join; joinReachable models that membership contract | Prove actual branch/loop construction and complete source-expression coverage; the model does not assume HIR extraction correct |

Bindings are review freshness evidence, not a substitute for semantic refinement. Changing a bound declaration requires model review and regenerated bindings. A reviewed hash still does not prove its production implementation agrees with Lean.

## Historical evidence and 2026-11-07 reconciliation

The original run recorded a successful pinned Lean 4.30.0 build and an independent 28-root axiom audit. Toolchain compiler commit: `d024af099ca4bf2c86f649261ebf59565dc8c622`, arm64-apple-darwin24.6.0. The initial 24-root model passed its first build; the approved Write extension produced the final 28-root model in a second changed-model build. These are historical results, not execution against this new release-based candidate.

The original `/private/tmp/release100-ownership-flow-write-lean-build.log`, `/private/tmp/release100-ownership-flow-write-axioms.log`, and temporary formal-audit report are now missing. Their previously recorded output hashes remain in `source_bindings.sdn` as historical records with explicit missing-output status; they are not represented as recoverable logs or fresh receipts.

The original worktree still retained native Lake build traces, copied byte-for-byte into the campaign's read-only evidence directory `/private/tmp/release100-eight-lane-20261107/lane9/evidence`:

| Retained artifact | SHA-256 | Evidence scope |
|---|---|---|
| `OwnershipFlow.trace` | `c56eecb378525b8b36789311eb080b90875f7db55b2294cc2e2132f1d1609f92` | Historical model compile command, exact Lean version/commit, input paths/internal hashes and output identities |
| `OwnershipFlow-Audit.trace` | `fbf96d12d4c0bf17f9d8c7256270d85ed1fd61555b694d94000ba954c8a5814b` | Historical native kernel reports for 28 exact roots, including Write lemmas; only `propext`/`Quot.sound`, no project or forbidden axioms in these reports |

`retention_manifest.sdn` describes the copying operation and absence of new execution. The evidence files are external campaign review artifacts, not files included in this nine-file candidate. Lake traces are local historical execution records, not remote attestations or a substitute for source/runtime refinement.

The model, Audit source, toolchain, package manifest and executable twin were extracted without modification from checkpoint `a324376253be34e74bac31bf1aecc27fa9a59183` (identical to rebased checkpoint `1fc8098f7d6ee0ddc1c62ae6cd658ee835359cc0`). The candidate base and exact source/model hashes are recorded in `source_bindings.sdn`. Both bound production sources in this release base match the recorded bytes: ownership solver `0b03fb4a47670b6474663741ace8e79598f9dd654ce12c565f2d499591cd8919`; borrow graph `c8fbeebe3f73c53371c638c8b2e057e6c9e47b88552f77b923f87a0764d118c2`. This establishes byte identity with the reviewed source bindings, not execution of the current compiler or proof of compiled behavior.

No Lean build, proof, Simple test or runtime qualification was rerun for this candidate. Historical proof evidence applies only to the unchanged model statements; current candidate execution remains NOT_RUN and full FV-OWN-02 remains OPEN. The generic shell guard's former successful status is recorded but its original stdout cannot now be inspected. The retained Audit trace supplies inspectable historical kernel output without inventing a replacement receipt.

## Executable twin and remaining admission

`test/00_formal_verification/compiler/ownership_flow_transfer_refinement_spec.spl` calls the actual production transfer/coverage/overlap functions and OwnershipFlow.check. It covers existing-hazard preservation, idempotent Move, covered versus uncovered/ancestor revival, conservative symbolic indices, distinct constants, negative moved reads, positive separate-base reads, reachable predecessor order, terminal exclusion and fail-closed work budget. These are real behavioral assertions, not source-text/hash checks. Execution remains NOT_RUN.

The matching manual is authored pending generation; it is not generated evidence. When a qualified runtime exists, run the exact twin once, retain executed cardinality/runtime identity, generate its mirror with SPipe and review it. Add independent sabotage controls for changed overlap/coverage/merge/read logic in an isolated capped worktree; do not mutate this shared active checkout.

For the full plan still prove rooted unique ownership, moved/uninitialized/dropped state refinement, original short-scope/overlap/reentrancy safety, cleanup/fallible transfer, regions/finite-generation handles, fused/split cleanup, exact cache identity, reader quiescence and failure reservations. Add the independent protected FV/AC/route baseline and candidate-bound mutation receipts. No broad ownership, no-GC default, interpreter parity, cleanup or release PASS follows from this focused theorem set.
