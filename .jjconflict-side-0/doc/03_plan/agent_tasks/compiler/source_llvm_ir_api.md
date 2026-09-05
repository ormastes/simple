# Source-to-LLVM IR agent tasks

<!-- codex-design -->

- **Primary implementation owner:** Codex lane
  `/root/compile_stub_real_api_103`.
- **Parallel sidecar lanes:** N/A for implementation; one xhigh reviewer is
  assigned read-only topology and final-diff review.
- **Shared interfaces fixed before review:** `CompilerSourceLlvmIrResult`,
  `compile_source_to_llvm_ir`, `cli_compile_source_llvm_artifacts`, explicit
  target scalars, and explicit MIR entry policy.
- **Manual/SPipe helpers:** N/A; the user explicitly excluded SPipe and all
  execution gates for this lane.
- **Merge owner:** parent agent `/root`.
- **Final reviewer:** xhigh `gpt-5.6-sol`, static review only.

Dependency order: target authority -> explicit MIR lowering -> compiler API ->
CLI facade/callers -> Rust ABI deletion -> contract spec -> final static review.
