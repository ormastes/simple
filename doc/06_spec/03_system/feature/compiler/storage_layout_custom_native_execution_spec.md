# Custom-native storage-layout execution

This scenario proves that one logical fixed-record field can use distinct AoS
and SoA physical addresses without changing its load/store result.

The native function computes an affine address from runtime index `3`, stores a
64-bit value, loads it, and returns it. Independent expected addresses are AoS
`8 + 3 * 24 = 80` and SoA `40 + 3 * 8 = 64`.

Evidence includes multiply/add/load/store selection, emitted bytes, W^X
transition, exact little-endian mapped bytes, the untouched alternate-layout
address, and adjacent canaries.

Current status: the loader now uses canonical exact-width `rt_ptr_read_u8`, but
the scenario must be rerun with a freshly rebuilt runtime containing that
symbol. A native runner that fabricates unresolved assertion/helper stubs is
not evidence. A PASS requires one executed example and
`STORAGE_LAYOUT_NATIVE_PARITY_PASS`.
