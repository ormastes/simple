# Generic alias call linkage differs from its admitted provider

Status: candidate; repaired-producer native proof pending.

The actual two-spelling generic fixture compiled through HIR and MIR under
admitted attempt9 c903, then linking failed. The consumer object references
compiler.core.provider.identity$i64, while the provider defines
compiler.frontend.core.provider.identity$i64. The ordinary function call and
provider both use compiler.frontend.core.provider. Retained evidence is at
/tmp/simple-hir-owner-admitted-alias-green-c903-20261030/probe.log and its objects.
The two selected source files matched the frozen target's SCV audit; no linked
artifact existed. The separate seven-case overlay normalization probe passed,
but that does not qualify this generic call route.

specialization_callee_name_v1 used the logical template dictionary key as the
native owner. Logical aliases remain valid lookup keys, but the admitted module
path identifies their physical provider. The repair derives only the emitted
cross-module specialization owner from module_paths, falling back to the
existing key when no path exists. Extern and global linkage and same-key local
calls retain their existing behavior. MIR NamedVar and backend symbol handling
remain unchanged; no global compiler.core rewrite is introduced.

The typed production process_modules regression checks both a numbered physical
provider reached through the historical alias and a distinct real unnumbered
overlay. Existing synthetic module fixtures now use paths consistent with their
logical owners, so they model physical declaration emission honestly. The
already-existing actual admitted_alias_case fixture is the end-to-end native
regression and must link and execute under a rebuilt producer before qualification.
This complements the prior physical ownership metadata fix; passing strict RTI
registration alone was not sufficient to establish native linkage correctness.
