# Cosmos NFC pure-policy migration audit — 2026-08-19

## Scope and boundary

This lane preserves `cosmos_nfc.c` as the sole owner of volatile DMA/MMIO,
atomic channel/ownership state, barriers, bounded polling, pointer validation,
and command ordering. The already-migrated `cosmos_nfc_decode_ecc` acquisition
bridge is unchanged. The new `cosmos_nfc_policy.spl` object accepts and returns
only fixed-width `u32`/`i32` scalars and has no per-operation allocation path.

The public C firmware ABI and the layouts of `cosmos_nfc_io` and
`cosmos_nfc_ecc` are unchanged.

## Pure-Simple owner inventory (28 scalar exports)

| Group | Pure-Simple decisions |
|---|---|
| Address/target derivation | channel base; row validity; channel/way/row target validity; erase-row alignment |
| DMA admission | generic bounded range; data; raw-data; spare; completion; status; error-info; toggle; half-open overlap; reservation-argument bounds |
| Timeout quarantine | whether DMA ownership releases; whether a channel becomes terminally faulted |
| NAND status | shifted NAND status and `INVALID`/`UNAVAILABLE`/`OK`/`HW_ERROR` decode |
| Operation composition | normal IO and raw IO validity; initialized gate; contract gate; locked-channel gate |
| Init state | initialized/failed/continue state; self-test mapping; contract propagation |
| Terminal transfer state | nonzero raw-completion decode |
| Toggle policy | the three GreedyFTL V2FEnterToggleMode payload words |

The C bridge directly acquires the status-report done bit and zero raw
completion word inside the existing hot polling loops. Those two acquisition
checks are intentionally not cross-object calls: the loop bounds, MMIO/DMA read
count, channel/way order, and terminal policy call count therefore remain
stable.

## C-owned inventory

- ownership and channel spin locks plus atomic state storage;
- fixed five-range DMA ownership table and commit/clear mechanics;
- PL contract MMIO acquisition;
- channel-accept, way-ready, and controller-idle polling;
- command register writes, barriers, and status-command scheduling;
- volatile completion/error/status acquisition;
- reset/set-features sequencing;
- public synchronous read/raw-read/program/erase/status/init orchestration;
- existing ECC acquisition/ABI bridge.

## Evidence contract

`scripts/check/check-cosmos-nfc-policy.shs` fails closed unless the compiler has
an admitted Stage-4 provenance receipt. Once admitted, one run must establish:

1. 5,005 comparisons with an independent frozen pre-migration C oracle;
2. 29/29 named runtime decision outcomes from the production Simple predicates;
3. an exact 28-function scalar export set and empty undefined-symbol closure;
4. no entry/runtime/allocator definition in either policy object;
5. ELF64 x86-64 host and ELF32 ARMv7 Cortex-A9 relocatable object guards;
6. the unchanged public C function signatures and struct layout guards;
7. all 27 production-used policy exports present as undefined imports in the
   compiled `cosmos_nfc.c` bridge object (the generic range export is oracle
   and direct-policy coverage only).

Host evidence is not physical NAND, DMA-coherency, ECC-margin, or board
evidence. Production and focused links must add the closed
`cosmos_nfc_policy_simple.o` object; that shared wiring is deliberately left to
the merge owner for this isolated lane.

## Current execution state

The first gate attempt on 2026-08-19 exited `BLOCKED` before Simple compilation:
the lane compiler symlink had no canonically admitted Stage-4 provenance
receipt. No Rust-seed or Stage-3 fallback was used. C bridge/ABI warning-clean
compilation passes independently; runtime parity and target-object evidence
remain blocked until the external Stage-4 admission exists.
