# NB-10: bounded nominal diamond flow

Requirement: the selected C2 aggregate-flow continuation in lean_nominal_body.md. Prerequisite: reviewed draftPR4018 exact c151cf021dfa8038cffcce8954e8a6a3fe49de4d; current captured release3ce093e is separate. This source packet is an increment, not full C2 or formal qualification.

## Single owner and flow

Only plugins.backend_lean.lean_nominal_body changes production. The existing public translate_mir_nominal_body API and both backend export facades remain unchanged. LeanNominalFlowPlan adds trailing join_path with empty default. The existing terminal path is selected when join_path is empty.

The planner validates block identities once. It follows the prefix to Ret/If, then walks each arm using a fresh visited dictionary and a read-only forbidden prefix map. This preserves exact cycle/prefix-backedge rejection. A then-path position index finds the first shared else block; the remaining ordered suffixes must match exactly. It splits exclusive prefixes and one shared suffix without recursive path enumeration. A scalar unique count, not Dict.len, proves complete coverage. Separate returns remain the existing NB09 shape. Unsupported terminators, nested branches, missing/disconnected blocks and cycles reject before body emission.

## State and binding

The Bool condition is checked/consumed first. diamond_lines uses existing fresh fork_for_branch maps and instruction_lines for exclusive arms; returning_path is deliberately reserved for the common function-result suffix. Both arms succeed before any merged state is installed. Assigned union retains definition history; live intersection admits only values present and unconsumed on both arms. Existing bind rejects redefining prefix assignments, so unchanged dominating locals can stay outside the conditional.

Only newly arm-defined both-live locals are transported, in body.locals order. Unit transport emits a typed ignored let; one value emits an exact typed variable; multiple values emit a typed tuple pattern, with each product element parenthesized to preserve compound-type precedence. Arm instructions and their transport expression are nested beneath the emitted conditional. No untaken-arm evaluation or hoisted effect is introduced. The shared suffix is emitted once with merged maps, exact return typing, and existing read/move/no-redefinition checks. Drop, mutable stores, calls and other unsupported operations still refuse; no native destruction semantics are inferred.

Types/context maps remain read-only shared metadata. Branch and merged assigned/live maps are separate allocations. Logical planner cost is O(V+E) for this fixed shape, plus O(L) for forks/join, plus existing type validation and emitted-source work. A common suffix can be traversed twice during planning but is validated/emitted once. No repeated whole-module scans, persistent registry or proof cache is introduced. Runtime allocation/copy costs, RSS and performance are unmeasured.

## Oracles and limits

40 new mirrored public API scenarios are authored UNRUN. Existing invalid branch fixtures now report missing live definition, suffix redefinition or disconnected graph instead of a blanket shared-block refusal; assertions are retained and fixtures unchanged. Module exports return Err without a published Lean value on any arm/suffix refusal; export_function's pre-existing builder comment behavior is not called transactional.

No compiler, Lean, proof, native or SPipe execution occurred. C1 authentication, C2 broader CFG/union/recursive fixed Vector/calls/mutation, C6 trusted replay and C7 physical/runtime refinement remain OPEN. Existing logical source GOs are reused, never relabeled runtime acceptance. Maximum3 independent source-review cycles apply to this increment.
