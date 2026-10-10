# Optimizer exception destinations and Send uses

Source: `test/01_unit/compiler/mir_opt/call_terminator_unwind_destinations_spec.spl`.
Status: **AUTHORED_UNEXECUTED**. The qualified compiler has no test subcommand;
the CUDA native candidate crashes during MIR lowering before a runner is built.

| Scenario | Assertions against actual optimizer functions |
| --- | --- |
| Copy propagation | Retains call destination 3, one argument, normal edge 6, unwind edge 7, payload destination 8 and type-tag destination 9. |
| Successor analysis | DCE and outlining each return exactly normal edge 6 followed by unwind edge 7. |
| Call uses | Outlining reports callee local 4 and argument local 5, excluding exception destinations. |
| Send uses | Outlining reports target local 11 and message local 12, excluding result destination 10. |

These are authored behavioral regressions, not evidence of test execution.
The CUDA closure's separate 157-module HIR and monomorphization checks do not
prove these assertions. See
`doc/08_tracking/bug/cuda_optimizer_surface_owner_2026_10_10.md` for retained
build evidence and unresolved gates.
