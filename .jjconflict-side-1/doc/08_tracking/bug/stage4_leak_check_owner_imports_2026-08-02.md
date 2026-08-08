# Stage4 leak-check owner imports

## Reproduction

After native-safe HIR dictionary counting landed, Stage4 stopped with two real
HIR diagnostics in `src/compiler/tools/leak_check/main.spl`: unresolved
`interpret_file` and unresolved `MemLeakEntry`.

## Cause and fix

The tool imported both names through broad, multi-hop facades. Entry-closure
HIR lowering did not recover their defining owners through those chains. The
tool now imports `interpret_file` from
`compiler.driver.driver_public_interpret_bridge`, `CompileResult` from
`compiler.common.driver_core_types`, and `MemLeakEntry` from
`std.mem_tracker.types`. Adjacent memory-tracker operations remain on their
implemented public facade.

## Regression evidence

`leak_check_owner_imports_spec.spl` locks the concrete call/type owners and
rejects the two former facade import shapes.
