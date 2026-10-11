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

The enum and promotion helper live in the dependency-free
`compiler.hir.hir_lowering.phase_memo_ownership` module. `types.spl` imports
that module, preserving the root set and driver failure behavior. The lifetime
spec imports the small helper directly, rather than importing `HirLowering`
and the parser/provider graph. Its boolean checks use the allowed
`to_equal(true/false)` matchers.

The source regression pins original owners, exclusions, scalar guard and
failure propagation. The native lifetime spec covers all seven payload families,
repeated aliases, reads after scope release, second-scope dictionary growth and
refusal without an active scope. The standalone fixture
`test/fixtures/compiler/phase_memo_ownership/main.spl` covers those contracts
without SSpec allocations inside active transient scopes. It includes shared
array payloads, a dynamically allocated string, 64 new dictionary keys in the
second scope, and refusal before and after the active scopes. Its 25 positive
guards increment a receipt counter and emit
`phase memo ownership: 25 checks passed` only after all succeed; each failure
has a distinct nonzero exit code.

Neither Simple spec nor the fixture has been executed for this patch. Native
execution must use a real Pure-Simple producer and bind runtime/provider and
source identities; interpreter extern stubs are not acceptable evidence.
No native job was launched while the frozen compiler matrix remained active.
