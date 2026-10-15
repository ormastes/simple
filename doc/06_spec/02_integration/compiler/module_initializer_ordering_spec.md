# Concrete module initializer declaration ordering

Authored manual; SSpec execution and generated docgen remain UNRUN pending an admitted pure compiled test host.

| Requirement | Actual exercise | Required result |
| --- | --- | --- |
| REQ-MODULE-INIT-ORDER-002 | Parse call-initialized globals; pass reversed declarations and synthetic equal-span/equal-ID inputs through the actual ordering owner. | Declaration order, ID tie-break and stable equal keys; literals excluded; input unchanged; empty and singleton arrays preserved. |

The native MC/DC behavior probe invokes this same helper before its existing lowering assertions. The earlier native compile failed at generic inference before any assertions; the updated source requires new source-matched native execution. The local typed insertion sort is an explicitly recorded workaround with O(n²) comparison cost per module's dynamic globals, not a generic inference fix or performance claim.

Final bounded evidence (2026-10-16): the small Cranelift storage/positive-recording fixture and LLVM planner startup passed. The larger native compiler-behavior probe completed HIR/monomorphization but stopped during MIR64/413 with semantic failures and RSS exit88; none of its assertions executed. This SSpec and generated docgen remain UNRUN. The supervisor and separate terminal assessment in `.simple/storage/build/phase3-mcdc-initializer-export-20261015/` preserve the distinction. These documentation updates postdate the frozen producer snapshots.
