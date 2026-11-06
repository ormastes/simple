# Ownership-flow model and refinement admission

2026-11-06; release lane baseline `77b05b3a4fb6a3cb3c5b92c2b74cea56b4799b74`. This is a focused **MODEL_PROVEN** result contributing to FV-OWN-02, not closure of FV-OWN-02 or any other full memory-plan obligation. The production Simple twin is **NOT_RUN** pending an admitted runtime. All 12 full FV obligations remain open.

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

## Executed evidence

Lean toolchain: installed `leanprover/lean4:v4.30.0`, compiler commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, arm64-apple-darwin24.6.0. No Rust seed, Simple runner or compiler rebuild was used.

1. `BUILD_TIMEOUT=120 sh scripts/check/check-lean-proofs.shs --project src/verification/ownership_flow verification/ownership_flow` — exit 0; one project, two Lean source files, zero lexical trust bypasses. The initial 24-root model passed on cycle 1; the approved Write event extension required a second changed-model build.
2. From the project directory: `lake env lean src/OwnershipFlow/Audit.lean` — exit 0; all 28 explicitly listed theorem roots reported by the Lean kernel.
3. Independent exact-root report comparison — 28 expected/28 observed; no missing/extra roots; assumptions only the reviewed standard logical primitives `propext` and `Quot.sound` (allowlist also permits `Classical.choice`, unused here). No project axioms, `sorryAx` or `Lean.trustCompiler`. Full audit rows and output hashes retained in `source_bindings.sdn`.

Raw local logs: `/private/tmp/release100-ownership-flow-write-lean-build.log` and `/private/tmp/release100-ownership-flow-write-axioms.log`. The Lake project explicitly declares both model and Audit roots so ordinary `lake build` cannot omit the audit module. The generic shell gate alone is not asserted to enforce a transitive axiom policy; the independent root-by-root audit above supplies that evidence for this exact model.

## Executable twin and remaining admission

`test/00_formal_verification/compiler/ownership_flow_transfer_refinement_spec.spl` calls the actual production transfer/coverage/overlap functions and OwnershipFlow.check. It covers existing-hazard preservation, idempotent Move, covered versus uncovered/ancestor revival, conservative symbolic indices, distinct constants, negative moved reads, positive separate-base reads, reachable predecessor order, terminal exclusion and fail-closed work budget. These are real behavioral assertions, not source-text/hash checks. Execution remains NOT_RUN.

The matching manual is authored pending generation; it is not generated evidence. When a qualified runtime exists, run the exact twin once, retain executed cardinality/runtime identity, generate its mirror with SPipe and review it. Add independent sabotage controls for changed overlap/coverage/merge/read logic in an isolated capped worktree; do not mutate this shared active checkout.

For the full plan still prove rooted unique ownership, moved/uninitialized/dropped state refinement, original short-scope/overlap/reentrancy safety, cleanup/fallible transfer, regions/finite-generation handles, fused/split cleanup, exact cache identity, reader quiescence and failure reservations. Add the independent protected FV/AC/route baseline and candidate-bound mutation receipts. No broad ownership, no-GC default, interpreter parity, cleanup or release PASS follows from this focused theorem set.
