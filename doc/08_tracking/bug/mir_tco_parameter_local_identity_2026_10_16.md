# TCO confuses signature types with argument storage

Status: isolated source repair prepared; native and BDD controls UNRUN.
Qualified bug database reconciliation is pending a qualified full CLI.

The C1 Phase3 failure with producer0cd6d7c598f20af768774d68bc434f6a0b6660f6194a2e34e7eff48946e1aa9b
reports ambiguous bare Call matches at tco.spl108/173, followed by two empty
runtime-identity diagnostics and a MirInstKind.Copy payload mismatch.
The same source blob e65348204872c01e82f10ccbad1784ad00366796 is present
at C1 and1986eb71e4ad. Missing identities are cascading diagnostics here;
they do not prove 98 independent enum-registry bugs across the main build.

The concrete type error selects func.signature.params[index] (MirType)
as the destination of Copy, which requires LocalId. Call's destination is
also optional and must be checked before comparing the returned operand.
Indexed instruction declarations are retained explicitly before qualified
MirInstKind dispatch; their temporary bootstrap annotations are tagged.

The repair locates actual LocalKind.Arg(index) storage, rejects missing or
duplicate argument indices, and preserves calls needing a parallel-copy
permutation or move/constant lowering. Sequential copies of swapped
parameters would change values, so unsupported transformations retain their
original call and return. Statistics count only actual Goto transformations.

The public tco_run_on_function adapter remains unchanged; it currently returns
its input. This repair does not claim to enable the pipeline optimization.
Controls call the actual TailCallOptimization implementation with nontrivial
local IDs, test exact assignment identities, reject swapped arguments and
void/unrelated return cases, and use scalar checks rather than record equality.
MirBuilder supplies the complete function declaration before test overrides.

No native build, link, runtime PASS, compiler-generation completion or landing
is claimed. Qualification must use a frozen source and genuine producer/runtime
lineage, with at most three verify/fix cycles and no fake objects or stubs.
