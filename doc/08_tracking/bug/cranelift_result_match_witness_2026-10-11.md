# Cranelift rejects a verification-only Result match witness

The cycle3 compiler (`54f23cb2274e43f781138a7c110ebcd3a421fb958337e5624d615af6a7fe9da3`,
source `6bffb3135df`) aborts the LSP native build in
`compiler.common.cache_contract.virtual_source_read_registry_v1` with
`E-BACKEND-CRANELIFT-INST-ResultMatchSemantic`. Retained evidence is
`/home/yoon/dev/phase2-six-results-20261011/permanent-repair/patched-producer/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/lsp_build.log`.

## Cause and repair

`mir_instruction_kinds.spl` declares this instruction a verification-only witness
with no runtime effect. `switch_operators_calls.spl` emits it into the merge block
after constructing the discriminator CFG, payload bindings and arm result copies.
Commit `838f5e2e08c` already added named witness arms in LLVM, C, x86 instruction
selection and the MIR interpreter. Cranelift was omitted and its fail-closed
fallback panics on the otherwise completely lowered match.

Add the same named metadata-only arm to Cranelift. No executable operation is
removed, no Result representation changes, and no runtime call or allocation is
added. MIR emission and Lean verification consumption remain intact. The general
unsupported-instruction diagnostic remains fail-closed.

Extend the existing source gate to include Cranelift and update its C/Lean paths
to their current plugin locations. The new native fixture checks both arm orders,
two distinct success payloads, distinct error payloads, and post-match
continuation. Its negative mode
changes the expected error payload and must exit 2; ordinary execution must exit
0 with `result-match assertions=6 PASS`.

## Verification and dependencies

The source gate passes eight checks, including its fatal mutation self-tests;
the Cranelift-specific check requires a separate arm containing only the metadata
no-op. Whitespace validation passes. Native fixture
execution and the original LSP build remain pending. No compiler/native build was
launched for this repair: disk availability is below the coordinated 20 GiB floor.
Runtime verification requires a producer containing the adapter change, its bound
runtime authority, and separate producer-qualified caches for Cranelift and LLVM.
The fixture depends only on the standard Result representation, text runtime and
CLI argument facade. It does not need the virtual-source registry or its globals.
The original LSP build can still expose independent blockers after this one.
