# Custom-native storage-layout execution

This scenario proves that one logical fixed-record field can use distinct AoS
and SoA physical addresses without changing its load/store result.

The native function computes an affine address from runtime index `3`, stores a
64-bit value, loads it, and returns it. Independent expected addresses are AoS
`8 + 3 * 24 = 80` and SoA `40 + 3 * 8 = 64`.

Evidence includes multiply/add/load/store selection, emitted bytes, W^X
transition, exact little-endian mapped bytes, the untouched alternate-layout
address, and adjacent canaries.

Current status: blocked before scenario execution by the deployed native
runner's existing failure to compile `smf_mmap_native.spl::ptr_read_u8`. A PASS
requires the scenario to emit `STORAGE_LAYOUT_NATIVE_PARITY_PASS`.
