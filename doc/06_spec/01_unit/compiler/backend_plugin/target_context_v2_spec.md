# Retained builtin target context V2

Requirement: REQ-010. Selected scope: Feature A / NFR N2.

Executable: `test/01_unit/compiler/backend_plugin/target_context_v2_spec.spl`.
This is a manually maintained scenario companion, not a generated execution report.

| Scenario | Observable check |
|---|---|
| Driver default CPU | Empty AOT CPU matches the admitted `generic`; `native` does not silently replace it. |
| Feature request isolation | Mutating the caller's array does not change the retained feature list; module and AOT emission reject unconfirmed features. |
| Cranelift CPU limitation | Module and AOT calls reject a non-generic CPU before the triple-only ISA API runs. |
| LLVM module header | Generated IR contains the exact retained Linux triple. |
| O1 identity | Admitted `o1` remains Basic/-O1 through AOT preparation; changed operation optimization is rejected. Legacy unretained O1 mapping remains Size. |
| Module and AOT objects | Real LLVM emission yields ELF64 objects whose machine field is x86-64 on both paths. |
| Scalar object publication | A changed operation CPU publishes no object; matching CPU emits ELF64 x86-64 bytes through the existing scalar emitter. |

The positive object scenarios require a working LLVM `llc` and source-compatible
self-hosted test runtime. They fail rather than substituting fixture objects.
Run the spec once normally and once with `SIMPLE_BOOTSTRAP=1` to cover the
distinct target-argument branch, using separate stage-scoped evidence.

Acceptance remains `Unknown`; these scenarios do not prove backend-confirmed
features, instruction inspection, executed SIMD, or NFR performance thresholds.
The parent `session_authority_v2_spec.spl` covers exact result lifetime and
`Unknown` projection; this change does not alter that owner or V1 receipts.

Validation on 2026-09-28: executable scenarios **unrun**. The isolated worktree
contains no `bin/simple` or admitted release runner. An older shared binary is
not a source-compatible substitute. See the implementation plan for remaining
compiler/MCP smoke gates.
