# Typed nominal body lowering

1. Detect nominal Aggregate or field projection. Delegate other bodies unchanged.
2. Preflight a unique nonnegative block-ID index and follow entry_block through Goto edges to one Ret; reject missing targets, cycles, unsupported terminators and any unvisited block. Require a known nonvariadic signature, unique local IDs, and one exact-typed argument local per parameter index.
3. Retain exact types in the local table; arguments start assigned/live.
4. For each supported instruction, validate operands and destination before returning a typed let. Struct operands follow field order. Enum selection searches the discriminant value. Projections use the retained field name/index. Copy preserves source liveness; Move consumes it; destination reassignment errors.
5. Validate Ret against the exact signature return type; Ret(nil) requires Unit. Publish the joined body only on success.

Nominal equality includes raw SymbolId in the module's admitted context, and primitive equality preserves signedness even where Lean representations share a width. Definition/kind mismatches and unsupported types are errors. The context is the result of the existing module declaration planner; this packet introduces no serialization/admission API for untrusted externally fabricated contexts.

The new public translator receives MirFunction because MirBody alone lacks params_known, signature parameters and entry_block. Existing actual module APIs derive both from the same function. No physical memory equivalence claim is made.

Rendering: both LeanBuilder.emit_def owners indent every physical body line while preserving existing relative indentation. The semantic body translator remains indentation-neutral; emit_def_with_termination delegates to this corrected boundary. Direct builder oracles and full/generated module output assertions cover the correction.

## Mixed scalar/nominal lowering

Source evidence: lean_mir_translate already admits the exact scalar spellings in translate_binop/translate_unaryop and refuses signedness-sensitive operators. The nominal emitter previously rejected every BinOp/UnaryOp. New arms call those shared helpers, then check an explicit type/operator allowlist before rendering. Integer equality retains MIR signedness even though equal-width signed/unsigned integers share a Lean BitVec representation.

Both operands are rendered through the existing typed/live operand method, in left-to-right order; a moved left operand cannot be reused as the right operand. Result binding uses the same exact destination/single-assignment check as nominal construction. All emitted operands are parenthesized. No new primitive mapper or untyped fallback is added. The actual module paths from the preceding packet already invoke this owner; no further backend entrypoint change is needed.

Per-instruction work adds constant classification plus existing exact type comparison. No filesystem/process/environment APIs or global state are added. Performance remains unmeasured. No additional compiler or runner attempt is authorized; source and API review are distinct from execution.

## Linear path extension

The NB-08 continuation is specified in [lean_nominal_linear_flow.md](lean_nominal_linear_flow.md). One emitter consumes the validated block-index order, retaining its exact types, assignments and move liveness across edges. The existing scalar fallback and supported instruction set are unchanged. This replaces only the prior one-block admission restriction; it does not admit general CFG or mutation.

## Terminal branch extension

NB-09 is specified in [lean_nominal_terminal_branch.md](lean_nominal_terminal_branch.md). A shared preflight validates either a linear path or one terminal If whose two successor chains are disjoint and returning. Prefix instructions and the exact Bool condition are processed before two explicit fresh mutable-state maps are constructed. Both arms retain the same read-only type/context facts but independent definitions and move state. No general merge or nested-branch semantics is inferred.
