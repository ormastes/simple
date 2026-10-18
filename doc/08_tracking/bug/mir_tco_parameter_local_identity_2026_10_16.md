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

## Focused native qualification, final cycle3

Frozen tested source: c532e1fe49a5ab647fe8ae396d34303b4e4e614d. Exact bootstrap producer 0CD6D7C598F20AF768774D68BC434F6A0B6660F6194A2E34E7EFF48946E1AA9B built the actual shared fixture and TCO implementation using the original persistent entry cache with ordinary source invalidation. Parse18/18 and HIR10/10 completed without reported failures; actual canonical response selected85 SPL COFF objects from the110-module parse closure. All85 selected object paths were new versus the retained cycle2 manifest; no producer cache-hit count is inferred.

The independently reviewed strict link used those85 objects,38 unchanged own-D9 C objects with freshly checked391-header/source/object/compiler proof, and the canonical /MD entry with14 actual initialization roots. Link exit0/log0; no FORCE/IGNORE. Strict candidate SHA256:088982F60891D6853141538AE9BA36905282FA4E0A1AF79E8DCE27631328F5BC.

Its authorized FIRST AND ONLY control execution PASSED: exit0, exact `PASS tco-local-identity` plus newline, stdout24bytes, stderr0, elapsed0.0378627seconds, no timeout, identical pre/post executable hash. The exclusive invocation ledger and both earlier crash receipts/executables/dumps remain preserved. No already-green run was repeated. This is the final shared qualification cycle3/3.

A PowerShell argv verifier initially constructed its comparison array incorrectly and FAILED CLOSED before linking; its failure receipt remains intact. A corrected verifier parsed the actual executed entry command and established exact argument equality before link. No entry recompile or unsafe bypass followed that failure.

Scope: actual TailCallOptimization shared controls, including false manifest presence before and after by-value transformation, PASS. This does not fix or qualify the baked producer nil guard, nor admit a new compiler. BDD and broad compiler/lib/MCP/LSP gates remain UNRUN; no Phase3 completion, deployment or merge is claimed. Evidence: external mir-tco-local-identity-native-cycle3/strict-link/{strict-link-receipt.json,control-run-started.json,control-run-receipt.json,control.stdout.log,control.stderr.log,strict-link.map}.