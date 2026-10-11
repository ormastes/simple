# Phase-wide HIR memo promotion repeats reachability walks

Status: focused source repair; native lifecycle and aggregate performance
validation pending. No RSS or elapsed-time improvement is claimed.

The frozen attempt-3 CLI build at source HEAD
`0e44a375a47985e6a3b7974a9378c694d5c888e3` parsed, committed and released all
2549 declaration surfaces. Its subsequent `hir-reexport` warnings occur during
HIR lowering, rather than proving a dependency-freeze stall. The log contains
`hir` progress at 626/2549 and elapsed 1590406 ms. Log location:
`build/bootstrap/stage2-compiler-tests/x86_64-pc-windows-msvc/verification/logs/compiler_cli_build.log`.
Warning frequency alone cannot attribute time or retained memory to reexport
resolution; no warning suppression or nominal-container exclusion is proposed.

`HirLowering.promote_phase_memo_transient_owners` promotes 49 collection owners
separately after every transient HIR scope, plus one guarded scalar text owner.
These owners include both dictionary and scalar-chain representations of growing
phase memos. In `src/runtime/runtime_native.c`, `rt_transient_heap_promote`
classifies persistent arrays/dictionaries as traversable, visits their children,
and builds a fresh traversal plan and seen set for each call. It frees that plan
before returning. This proves repeated graph traversal, not a retained plan leak
or a measured cause of the observed RSS growth.

The repair follows the existing `ModuleSurfaceRoot` pattern: 49 exact typed
owners become enum payloads in one root array. One collection promotion walk
can deduplicate shared children across the batch; the conditional scalar text
call remains separate because the empty literal can be unregistered. The
lowerer still owns the original memo fields across scope resets. No entire
lowerer, symbol table, provider registry, module-local scratch or diagnostics
graph is added to the root set. The carrier array is shallow-freed after either
provider success or refusal, and the provider result still propagates to the
driver's existing fail-closed path. Promotion refusal can now leave fewer
partially promoted collection owners, but cannot become success.

This pattern also promotes its enum wrappers. The native shallow array-free
operation frees only the carrier; wrappers have no enum-free API. Therefore
the patch adds 49 small persistent wrappers per call, as the existing surface
pattern does. It is a traversal optimization with an unmeasured carrier-memory
tradeoff. Aggregate RSS improvement must not be inferred from the call count.

Static evidence under
`C:/dev/simple-phase3-hir-memory-evidence/phase-memo-batching/source-root-parity.txt`
compares the original method in the frozen checkout to the private repair:
all 50 owners remain, 49 batch payload types exactly match field declarations,
and no collection owner is missing or duplicated. The collection call budget
is 49 to 1, with scalar behavior unchanged. Working and staged direct-env
guards and `git diff --check` are required before exporting the patch.

The source regression pins owners, root counts, exclusions, scalar guard,
carrier cleanup and failure propagation. The native lifecycle regression tests
all seven payload families, repeated aliases, reads after scope release,
second-scope dictionary growth and refusal without an active scope. Neither
Simple spec has been executed for this patch. Both require validation on a
real Pure-Simple producer; interpreter extern stubs are not acceptable evidence.
No native job was launched while the frozen compiler matrix remained active.
