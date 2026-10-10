# LLVM signature discovery rewrites and discards function bodies

Status: **OPEN — source correction proposed; runtime and performance gates
unexecuted**. No measured RSS/time improvement or bootstrap qualification is
claimed.

## Source evidence and correction

`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` runs two loops in
the normal module translator. The first collects function return and parameter
types; the second translates each function body. Before this change, both
called `llvm_bootstrap_ssa_function`, which performs alloca-based or variable
SSA rewriting. The first loop discarded those rewritten blocks after reading
the return type.

The correction removes only the first transformation. It retains the
`MirBody.from_function` owner boundary and `bootstrap_return_type` accessor.
`src/compiler/50.mir/mir_instruction_graph.spl` establishes that
`from_function` copies `func.signature.return_type` to `return_ty`, while
`MirFunction.with_blocks` preserves the signature. Both successful rewriting
paths return through `with_blocks`. The emission loop still performs the same
SSA transformation, so loop-carried and reassigned locals retain that repair.

The candidate originated in memory review commit
`26750539b` (base `b9ccb2ab9`). This isolated change deliberately excludes its
new cold-HIR admitted-carrier shortcut. Independent review rejected that
shortcut because a public caller could construct a valid-looking carrier with
an unrelated inventory/digest. The accepted driver cold-receipt checks remain
unchanged.

## Required execution gates

`test/fixtures/compiler/llvm_signature_discovery_single_ssa.spl` covers loop
reassignment and integer, bool, text, array, and void return types. Build and
run it with the old and rebuilt pure-Simple producers under normal AOT. Both
must print the fixture's six expected lines, in order. Also check generated
LLVM/objects for real function bodies and valid SSA. The fixture has not been
executed in this review.

Then repeat a representative previously slow module once with frozen input,
runtime, target, cache state, and resource limits; compare wall time and peak
process-tree RSS. Existing large-row timeout evidence stopped before codegen
and therefore does not measure this optimization's benefit.

Use ordinary tracing only. `SIMPLE_BOOTSTRAP_DEBUG=1` changes translation
semantics; see
`mir_to_llvm_bootstrap_debug_changes_translation_semantics_2026-07-13.md`.
