# Derived public text constants retain unresolved inference in cold HIR ABI

Status: OPEN compiler defect; explicit public interface types mitigate the MCP owner.

Producer: pure-Simple Stage2 SHA256 `2f34befeaca05b0cd4e389f4cda2e0d1558e15a8342f9b60f7fbacfa528830ae`.
Frozen source: `3d7141f912c1047854090f8e068c4214f0c61031`.
Original log: `/home/ormastes/simple-linux-bootstrap-build-20261009/local-release-diagnostic/mcp/build.log`.

Valid compact source: `pub val ASSISTANT_STORE_ROOT = ".build/llm_dashboard/assistant"` followed by `pub val ASSISTANT_STORE_SESSIONS = ASSISTANT_STORE_ROOT + "/sessions"`.
Native MCP build fails cold HIR receipt capture with `cold-hir-abi-unresolved:unresolved-inference:0:0:declaration=constant:ASSISTANT_STORE_SESSIONS`. No artifact is admitted.

Mitigation: declare all five exported assistant store paths as `text`, preserving their initializer expressions and runtime paths. This is a public interface annotation, not a compiler inference repair.

Removal/closure criterion: rebuild a pure-Simple producer with inference fixed; compile the original unannotated dependent text constants through cold HIR ABI receipt capture and native object generation, then run the output. A full MCP build against the annotated owner must also pass; source editing alone does not qualify it.

## Bounded diagnostic evidence

Fixture directory: `/home/ormastes/assistant-constant-inference-fixture`. Original unannotated native fixture reproduces cold HIR ABI rejection (`inferred.log`). Annotated five-path fixture produces a real LLVM relocatable object (`typed.log`, `typed.o`, SHA256 `c442f386fce47a818781e26e998a81a9bc3b01782c83e57ec08ee3f7081c8f65`).

A borrowed Hello entry omits this fixture's dynamic global initialization and exits 2; it is unsuitable for this fixture. A manually initialized DIAGNOSTIC entry executes all five exact path assertions, prints `assistant-store-paths-ok`, and exits 0 (`diagnostic-init-evidence.json`). This does not qualify the production entry or MCP binary.

The production LLVM-link attempt fails runtime source discovery in the standalone fixture. The configured Cranelift production attempt rejects the text global ROOT as non-scalar (`production-cranelift.log`), with no published binary. These remain distinct compiler/runtime boundaries. The newly added focused SSpec is not executed: existing qualified standalone test runner is unavailable. Full MCP and the focused SSpec require a subsequent compatible producer run. No full-bootstrap or MCP PASS is claimed.
