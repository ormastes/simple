# Imported struct parameter copying loses exact provider layout

Status: OPEN; no correction attempted after six-cycle limit.

Cycle6 source e4049c1437b and admitted producer e5434790d2374ca667f3e8432e439016d091336829883ed17db65e62cb70548c
compile the expanded imported-inequality fixture, but its executable exits22.
Two provider modules define ImportedModulo: a custom-equality value/marker type
and a plain prefix/value/marker type. Specific direct field and literal checks
pass before comparing marker55 against marker66 returns true.

Confirmed source path: Named Struct parameter_type_name remains the bare name
in _MirLowering/function_lowering.spl (Class alone is qualified). Plain value
parameters call copy_struct_value_recursive with that name. Its field loop,
aggregate operand count and result provenance use the bare row in
mir_lowering_stmts.spl; it does not preserve a local HIR note there. A two-field
row can truncate a three-field parameter. Exact later comparison behavior and
memory safety remain unproved; do not replace this failure with identity or
hardcoded equality.

Future correction must preserve the exact declaration through complete parameter
copying, recursion, aliases and local type provenance. Tests must independently
vary first, middle and last fields across same-named providers and both parameter
and array paths; the existing constructor checks alone cannot prove that boundary.
Keep the native exit22 reproduction and all candidate caches. No seventh cycle
is authorized by the current six-cycle instruction.

## User-authorized cycle7 correction

After the proposed three-cycle extension, the user replied `go`, then `go`
after an interruption. The cap is now nine total, with cycle7 current. The
private branch rebased cleanly onto release_phase3
3ce093ea597b9f413a37b4f838407da2e63efa7f. Prior six-cycle source/evidence remain
on work/items247-sixcycle-preserved-20261021. Upstream enum/archive/runtime
changes are retained; their presence does not qualify this combined candidate.

Both Isolated(Named) shape registration and ordinary Named Struct parameter
handling now use the exact declaration's registered composite layout. Class
handling remains separate. copy_struct_value_recursive transfers existing local
HIR metadata through the standard helper in addition to its layout provenance,
Result-owner and generic-instance metadata. MIR tests require two complete
three-operand parameter copies under demand and reversed eager registration.
The native fixture and its exit22 oracle are unchanged. These corrections and
assertions are authored, not runtime PASS; cycle7 qualification is pending.
