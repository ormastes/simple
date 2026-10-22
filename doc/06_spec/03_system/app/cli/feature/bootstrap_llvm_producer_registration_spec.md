# LLVM bootstrap producer registration

Execution status: **UNRUN**. An admitted general SPipe/docgen runtime is
unavailable. This manual describes the executable spec; it is not a generated
pass receipt.

Run the executable spec in a fresh process with the two explicitly hashed
LLVM producer projections described in
`doc/05_design/compiler/llvm_bootstrap_producer_installer_seam_2026_10_21.md`.

1. Install the real selected K1 table and verify policy `llvm`, two active
   entries, and LLVM-only advertised output.
2. Resolve the LLVM adapter through the actual active registry.
3. Request Cranelift, VHDL, C and Wasm; require the registry's
   `PLUG-E-NOTFOUND` result and the producer's matching request refusal.
4. Request a backend plugin; require `PLUG-E-UNSUPPORTED`.
5. Enter the real bootstrap native command body with an unavailable backend
   and with a plugin override against an existing valid hello source; require
   failure status 1 without relying on a missing-source error.

The scenario covers registration and request routing. Producer compilation,
real LLVM object output/link/run, full CLI compilation and all-feature parity
remain separate build-owner acceptance checks.
