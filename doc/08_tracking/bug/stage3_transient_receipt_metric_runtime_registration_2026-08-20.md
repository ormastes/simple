# Stage 3 transient receipt metrics missing from runtime registration

Status: RESOLVED 2026-08-20

The Stage 3 streaming receipt reads seven scalar transient-allocation metrics.
Both hosted `runtime_memory.c` and core `runtime_native.c` intentionally provide
the same zero-argument `int64_t` ABI so receipts retain the same meaning in
either runtime lane. Those paired providers are therefore admitted in
`scripts/check/runtime_symbol_lane_divergence_baseline.txt`; they are parity
implementations, not accidental competing policy owners.

The C providers and public header existed, but the Rust interpreter dispatch,
native ABI inventory, ELF resolver, and shared generated-provider inventories
did not contain the seven names. Interpreted streaming tests consequently
stopped at `unknown extern rt_transient_raw_table_capacity`, while provider/JIT
resolution depended on incidental platform symbol lookup.

The fix registers the complete seven-symbol family across those surfaces and
tests the exact `() -> i64` ABI, canonical C-backed interpreter values, direct
ELF addresses, shared inventory classification, and generated non-null static
provider entries.
