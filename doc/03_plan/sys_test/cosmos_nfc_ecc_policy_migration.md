# Cosmos NFC ECC Pure-Policy Migration Test Plan

Scope is only the Tiger4NSC two-word ECC decoder and its C acquisition ABI.

1. Check every production/focused `cosmos_nfc.c` link includes
   `cosmos_nfc_ecc_bridge.c` and `cosmos_nfc_ecc_simple.o`.
2. Admit a Stage-4 self-host compiler and require the emitted host/ARM objects
   to expose exactly the six scalar policy functions with no undefined symbols.
3. Compare the public C ABI against the frozen pre-migration oracle across
   CRC/spare states, all 256 counts, three page words, and unrelated bits.
4. Require full nonzero compiler-instrumented C-bridge branch outcomes and all
   five named Simple predicate outcomes.
5. Record board evidence as `separate-not-included`; reserve live NAND ECC
   strength, DMA, and power-loss evidence for the board campaign.

Host acceptance commands:

```sh
sh scripts/check/check-cosmos-nfc-ecc-link-wiring.shs
sh scripts/check/check-cosmos-nfc-ecc-bridge-coverage.shs
sh scripts/check/check-cosmos-nfc-ecc-policy.shs
```
