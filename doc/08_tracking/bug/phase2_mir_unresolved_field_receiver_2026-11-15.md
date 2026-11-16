# phase2_mir_unresolved_field_receiver_2026-11-15

The frozen Phase 2 compiler cannot infer the receiver type of a method call on an
indexed global (`expr_attr_extra_stores[0].get(i)`) or a field chain
(`jit.jit_mapper.map(...)`). MIR then reports `bare variant 'Ok' is ambiguous ...
type unresolved` / `unresolved method call`.

Modules: compiler.frontend.core._AstExpr.nodes, compiler.loader.module_loader_services.
Workaround: bind the receiver to a typed local and annotate the Result type.
Remove when the pinned compiler infers these receivers.
