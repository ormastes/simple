# SimpleOS 32-bit bootstrap contract architecture

`simpleos_target_v1` is the sole target identity and ABI catalog.
`SimpleOs32BitTargetProfileV1` composes those canonical values with one local
32-bit platform table containing only linker emulation, manifest paths, and
QEMU executable. `SimpleOs32BitBootstrapReceiptV2` is the only promotion input.
Validation first matches the receipt to its composed profile, then checks Phase
1/2 lineage and immutable hashes, and finally authenticates the ordered
nonce-bearing guest transcript.

Structural validation is not authority. Promotion calls
`simpleos_32bit_bootstrap_receipt_v2_authorized` with the expected receipt ID,
expected nonce, trusted key ID, and 32-byte Ed25519 public key. The signature
covers the target/ABI/linker tuple, phase lineage, all artifact/manifests,
QEMU identity and exit, nonce, receipt identity, and raw serial transcript.
This makes copied success text and cross-run replay insufficient.

The contract deliberately separates cross-produced guest execution from target-native compiler execution. The legacy v1 API remains compatible, and its target-native predicate remains false. No architecture-specific validator is introduced.

Profile triples and ABIs match the canonical target-native values in
`src/lib/common/contracts/execution/simpleos_target_v1.spl`. Freestanding
Clang/LLVM spellings remain build-provider details and are not a second public
target catalog.
