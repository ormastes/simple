# NB-09: one terminal nominal branch

Selected scope: generic formal C2 aggregate flow / C4 structured branches, REQ-MC-007. This is required continuation, not full formal completion. Source dependency is the reviewed combined18 packet at `/home/yoon/dev/robust-tdd-20261014/formal-c2-combined-20261020` (manifest d0a42bf059a5580c16cc24e38899e6ed26e01c404748049e0ce7e905a9b10cc7; composition GO c0c93e4a27a1b7b69deb4e52d562c2b865afd572de4870313e745291f72857c5). The new checkout has base af10a7acd2ffa5fe9e487cf3c5bd15fcc4aa5c2a plus those exact dependency images. Originals remain frozen.

## Fixed interfaces and authority

The public `translate_mir_nominal_body(MirFunction, LeanTypeContext)` contract is unchanged. `LeanNominalFlowPlan` records prefix indices, optional-by-sentinel branch index, and each arm's ordered indices. `nominal_flow_plan` validates a unique nonnegative block table, follows the actual entry/edges, and assigns each reachable block exactly once. A scalar admitted visit count enforces whole-body completeness; no Dict.len or keys snapshot is count authority. This rejects missing IDs, cycles, merges/shared blocks, nested branches, disconnected code and unsupported terminators before output emission.

`LeanNominalBodyEmitter.fork_for_branch(locals:[MirLocal]) -> Result<LeanNominalBodyEmitter,CompileError>` creates fresh assigned/live dictionaries and copies scalar Bool entries over the already validated local list. It verifies copied entries survived insertion. It never copies the mutable map handles or guesses that assignment/clone deep-copies. Types and LeanTypeContext are read-only shared; no emitter method mutates those maps. `instruction_lines` and `returning_path` preserve the existing exact-type and liveness rules.

The original emitter processes the prefix and Bool condition first. Move condition consumption is therefore present in both snapshots. Two independent forks validate the complete arms and exact returns, even when the condition is a literal. A successful result renders a standard Lean `if ... then ... else ...` expression, with physical indentation retained by existing backend builders. There is no path enumeration, state merging, constant-fold omission, partial-source publication or new trust gate.

## Source-backed storage and semantic evidence

`_MirLoweringExpr/method_calls_literals.spl:lower_dict_lit` calls `rt_dict_new` for each literal. The actual native `runtime_native.c:rt_dict_new` allocates a fresh dictionary header and entry buffer and returns a mutable tagged handle; `rt_dict_set` mutates that handle. Plain assignment is not independent backing storage. The pure-Simple interpreter's `expr/collections.spl:eval_dict` also creates a fresh literal map before populating it. These source contracts justify explicit fresh maps; no differential runtime or OOM experiment was executed. Copy verification fails closed when a required copied entry is absent, but this is not an allocator-failure or whole-runtime memory-safety qualification.

MIR `If` retains the actual condition operand and then/else BlockIds. The condition is checked against exact MirTypeKind.Bool before rendering. Lean4.30 `Init/Data/Bool.lean` includes Bool conditional notation (`ite_eq_false`), pinned as semantic syntax evidence only; no generated module/kernel run is claimed.

## Complexity and acceptance

Retained type detection walks signature/local type occurrences once (T total nodes, O(D) recursive stack for structural nesting), following only already admitted Array/Slice/Tuple/Result wrappers; nominal SymbolIds are leaves, not a traversal of recursive declarations. No nominal identity or validity is inferred by selection. Scalar-only Result and scalar-only bodies keep the existing translator.

Logical graph work/storage is O(B). Each block/instruction is visited once along one prefix or one arm; the two forks copy at most L local rows each. Logical additional state is O(B+L) and emitted text is O(I); no per-path graph duplication, repeated key snapshots or global caches. Existing type/declaration mapping, dictionary implementation and string allocation costs are unchanged and unmeasured. No latency/RSS/leak/OOM guarantee is asserted.

Two real SSpec files import the plugin and compiler backend owners independently. Their 20 scenarios each exercise full/generated export and exact direct body output on success. Controls cover ordered/reordered/prefixed arms, each arm moving the same source, condition Move, nominal return, unchanged linear flow; negatives cover condition/definition/liveness errors, both-arm signed returns under a literal condition, inherited redefinition, missing/shared edges, cycles/nesting/disconnected code and unsupported terminators. Tests were authored before production; predicted baseline RED is not observed failure. All 40 cases, previous suites, compiler/Lean/native checks, SPipe doc generation, memory/performance and core/MCP checks are UNRUN.

## Full C1–C7 ledger

C1 typed VIR/provenance and C6 exact trusted replay remain separate open production-qualification requirements, not inferred from text export. C2 now has prepared source for acyclic and supported positive recursive declarations, linear nominal flow and this terminal-branch increment. Recursive fixed Vector, unions, general branch/merge/phi/loop/enum-elimination/call/mutation semantics remain required and unsupported. Existing C3 effects/state/constraints and other implemented owners are preserved, not reimplemented or relabeled absent. C4 arbitrary CFG/termination/invariants remain open beyond the exact admitted shape. C5 proof closure is not obtained by source acceptance. C7 actual before/after refinement, native ABI equivalence and sabotage qualification remain open. Authenticated admission/policy/signing is untouched.

One author owns this isolated source delta. Independent Astra review is required with at most three source correction cycles; no builds or unqualified runner use is authorized. The stopped watchdog/memory-retirement lane remains untouched.

## Cycle2 admission correction (NB09-01)

The first revision required an incidental nominal Aggregate/GetField instruction and therefore left instruction-free nominal parameter selections on the refusing flat branch route. The corrected private `nominal_type_requested` detector checks retained return/parameter/local types and supported wrappers before the existing operation scan. Existing exact owner/type/argument checks still perform admission; the detector is not proof. Raw unsupported type families are not reinterpreted.

New controls contain no Aggregate/GetField: both declared Struct and Enum parameters are returned directly, or independently copied/moved to arm locals. Assertions bind literal qualified nominal signatures and terms. Unresolved symbol99 and enum-kind/struct-owner mismatch7 must fail in the direct body API and both public module APIs. Scalar-only and scalar-only Result identity functions preserve the previous route/output. The eight correction scenarios were authored before the production fix; all are UNRUN. This changes no branch shape, state-fork policy or trust boundary beyond closing the required selection gap.
