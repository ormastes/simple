# Backend target context V2: Stage 6A.1c propagation

Selected requirements: environment-optimized dynamic libraries Feature A / NFR N2,
REQ-010. This is a prerequisite to producer confirmation, not completion of 6A.1c.

Owner: backend acceptance agent. Merge owner and final reviewer: parent Codex
agent. Sidecars: N/A; narrow continuation stacked on PR #1835.

Keep `BackendCompileOptions` fields and V1 wire/receipt hashes unchanged. Retain
target configuration inside the builtin adapter; common AOT helpers still own
storage projection lowering, optimization, debug policy, and object emission.
LLVM header and command arguments use the same retained triple/CPU, including
bootstrap mode. Cranelift receives the retained triple but rejects non-generic
CPU requests while its ISA builder lacks a CPU negotiation API.

Nonempty features fail before emission; the V2 open gate remains unchanged.
PR #1827 separately owns early V1 constructor rejection. No acceptance enum or
receipt is promoted, and no implementation-identity claim is added.

Executable validation is blocked: this worktree has no admitted self-hosted
runtime. Pending: new spec (normal and bootstrap modes), parent session authority
spec, compiler/lib/MCP/LSP checks, MCP stdio integration, core runtime smoke and
MCP native smoke. Native positive tests must emit actual objects; no seed
fallback or synthetic evidence may mark these gates passed.

Acceptance/readback remains future work: LLVM's target-machine feature string
is creation input, not independent confirmation; Cranelift needs explicit ISA
builder acceptance output. LLVM-lib is not admitted by this builtin registry
and is outside this propagation slice. NFR measurements remain unclaimed.
