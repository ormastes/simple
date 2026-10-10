# HIR local and foreach bindings lose a proven enum owner

Status: reproduced before repair; proposed repair and SSpec scenarios UNEXECUTED.

Native authority: producer SHA256 `c6ce4632bbc5e1a3045a8a514a0c6fe8545e4ec5eb4215d90a7b430564c432f3`, compiler source `a487584ce`, native fixtures commit `a681ad90cd37cce2811e7245ca85d09cf586a72a`.
Actual receipts: `/dev/shm/simple-or-variant-probe-20261010/results2/summary.json` and per-case `build.log`, including linked runtime object hashes. These are diagnostic evidence, not matrix admission.

| Actual baseline case | Result |
| --- | --- |
| direct_mixed | Object/link/run PASS, output `1 / 1 / 0` |
| alias_typed | Object/link/run PASS, output `1 / 1` |
| alias_untyped | HIR failure, build exit 1; expected `1 / 1` unexecuted |
| typed_foreach | HIR failure, build exit 1; expected `2` unexecuted |
| untyped_foreach (array literal) | HIR failure, build exit 1; expected `2` unexecuted; additional inference gap remains |

Failing bindings report `or-pattern alternatives must bind the same variables`, with `[Deref]` versus `[]`. This is early HIR validation, not runtime enum ABI corruption. Bare units require an exact typed subject owner; payload patterns already carry their enum shape.

`statements.spl` discarded initializer type for unannotated val/var symbols and defined ordinary foreach symbols with nil type before lowering the body. Match lowering could therefore not recover the subject owner. The proposed change retains only a type already present on an expression (authoritative `has_type_`) or its exact Var/NamedVar symbol. It binds Array/Slice element types before lowering an ordinary loop body. Missing types remain missing. Explicit annotation representation, tuple iteration, OR binding validation and global name resolution are unchanged.

The direct array-literal foreach fixture remains outside this narrow proof: expression_core constructs ArrayLit with no expression type and nil element hint for nonempty arrays. It needs independently justified element inference, not an invented owner. No claim that this patch fixes that row or all Phase 3 failures.

Regression: `test/01_unit/compiler/hir/binding_subject_owner_retention_spec.spl` constructs actual AST declarations/loops and asserts exact owner IDs, enum pattern kinds and variant names. It covers val/var aliases, Array/Slice iterable aliases, non-authoritative placeholder rejection and a genuine mismatched binding negative. All new SSpec assertions are UNEXECUTED. Mutable aliases share the repaired declaration mechanism but have no native PASS claim.

Required next evidence: rebuild and pin the combined producer; execute previously failing alias_untyped and typed_foreach native rows with expected outputs, then execute the focused SSpec through a qualified runner. Preserve the genuine unrelated-owner negative and broader existing OR negatives. Existing green controls are retained evidence, not authority for the repaired producer. No full Phase 3 retry is authorized by this receipt.

## Final-cycle annotation presence repair

Cycle 1 producer `3dd3462384f8f43ad4920504d3f4e8b5321dbd89e5ab176fe9a885299a81a91e` from `8c5a9d767d28dda3b4fad76829a1272b722bc7e4` executed typed foreach correctly (`2`), but both val and var aliases of a typed E parameter still failed HIR. The alias initializers are parameters, not constructors.

Cycle 2 trace evidence: `/dev/shm/simple-phase2-subject-owner-first-loss-trace-20261010/first-loss-trace.json` and `validation/{alias_untyped,mutable_alias}/build.log`. No recovery/inferred trace was entered; before-define reported a nonnil type of kind `other`, owner -1, and the defined symbol's scalar owner stayed -1.

Source explains that boundary without an ABI guess: `_FlatAstBridge/convert_nodes.spl:263–265` returns a present `TypeKind.Infer` for absent type indices. Lines 1835–1877 pass that Type into both Val and Var. Therefore AST optional presence is not annotation presence, and the lowered nonnil Infer previously skipped the initializer-recovery branch. The final repair uses the AST kind's existing scalar discriminant helper to distinguish Infer from concrete annotations before lowering. Nil AST input defaults to Infer. Only Infer selects inference; explicit Named enum/Any annotations and Error nodes are not replaced. No global variant-name fallback is added.

Two new constructed SSpec scenarios cover present Infer placeholders in val/var and explicit enum/Any annotations. They are UNEXECUTED. Existing native `alias_untyped` and `hir_binding_owner_retention_probe` (`mutable_alias`) retain exactly their source forms and are final-cycle gates, alongside typed foreach. The final combined producer must compile/link/run the aliases with expected outputs and retain negative OR binding rejection. No separate diagnostic build or full Phase 3 retry is authorized here; if final qualification fails, retain evidence and stop this cause's repair loop.
