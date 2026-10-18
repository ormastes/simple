# MIR retained-owner inventory and guard drift

Bug ID: `mir_owner_inventory_guard_drift_2026-10-18`.
DB reconciliation pending: the qualified normal DB tool is unavailable.
Inventory diagnosis base: `2414f2755c76f1d22ffdceb546657db442d7e68d`.
Landing base: `afc7a68d38eb707058c4d5d540d5465222df03a7`; the already-landed
trait lookup root retirement is preserved unchanged.
Native verification is UNRUN; this is not an observed count of use-after-frees.

The existing guard checks 17 invariants and reports four failure groups. Two
driver-call findings are obsolete exact argument matching: the direct path now
uses concrete `scoped_hir`, provider modules and the entry flag; the fallback
passes provider modules. Eight reported unpaired errors are already closed by
the reverse-reference abort helper or follow the successful final scope end.
The helper unconditionally attempts both reverse-reference abort and scope end.

The inventory failure is real: declarations contain 190 explicit field roots,
while the owner helper covers 168. The 22 omissions comprise 16 heap-capable
fields and six scalars, not 22 demonstrated dangling reads:

- Four function-local maps are already reset before promotion:
  extern_result_locals, static_scalar_locals, generic_instance_field_types,
  generic_instance_field_struct_names.
- lower_emit_fn_values is the module's prescan/emission `.values()` scratch.
  Only those completed loops read it. Detach it before promotion so restoring
  the explicit root inventory does not add retention of the input HIR bodies.
- collection_literal_operands, collection_literal_ordinals,
  imported_global_initializers and exact_extern_signatures are module lookup
  state; their explicit roots are restored without additional lifetime changes.
- extern_fn_symbols, callable_text_value_abi and the three struct type-parameter
  maps retain their current metadata lifetime. No broad clearing is introduced.
- builder.module.collection_plan_explanations and target_context.collection_policy
  complete nested heap-capable coverage. Six scalar fields complete the guard's
  all-fields contract: devirtualized_calls, lowering_entry_module and the four
  non-text collection target policy fields.

The guard recognizes scoped receivers independent of argument arity and rejects
unscoped calls with any arguments. Cleanup checking follows indentation blocks,
accepts the abort helper only after validating its exact body, and does not let
a conditional sibling cleanup protect another error path. Seven new positive
and negative fixtures exercise these shapes, including an omitted defaulted
heap field and a broken helper. Existing inventory comparison is not weakened.

The executable function-inventory regression lowers real AST/HIR for two
modules, checks completed MIR functions/calls, retires the scratch root, and
re-reads the first module and original input after the second scope. Diagnostic
serialization is an instruction-graph comparison, not a lossless archive.
Native execution, all-object completion and RSS impact remain unverified.
