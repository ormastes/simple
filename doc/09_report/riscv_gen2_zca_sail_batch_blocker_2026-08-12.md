# RISC-V Gen2 Zca Sail batch integration status — 2026-08-12

The independent source checkout was acquired and verified at
`a33475aeb80090127433b5a8b30e717edaa19e71`. Its archive and
`model/extensions/C/zca_insts.sail` hashes match the checked-in oracle pins.

Generation remains fail-closed. This host has no `sail` compiler, and the pinned
model's normal CMake generation preserves emulator, configuration, and RVFI
entry points but does not preserve a batch API exposing
`ext_decode_compressed`, the compressed `ExecuteAs` result, and `encdec` for
all 65,536 parcels. Therefore no RV32/RV64 truth table was generated and
`oracle.lock` correctly remains `status=absent`.

`riscv-gen2-zca-sail-batch-adapter.shs` is the reproducible adapter envelope.
It admits only the pinned tracked-clean checkout plus a receipt whose hash is present
in the checked-in independently reviewed allowlist. The receipt binds the Sail
compiler version and hash, overlay source hash, build-script hash, model pins,
and executable hash. The allowlist is empty today, so self-asserted receipts
fail closed. The envelope validates ordered `0000..FFFF` input, invokes an
admitted executable, and checks TSV shape plus compressed/non-compressed length
and canonical-absence invariants. It contains no Simple, HWIR, or local
compressed decoder.

The remaining integration requirement is an independently reviewed Sail
overlay, compiled with Sail >=0.20.1, that exposes the model's own compressed
mapping and `ExecuteAs` canonical encoding as the batch executable. Until that
artifact and its receipt exist, the oracle is unavailable rather than replaced
by a correlated local implementation.
