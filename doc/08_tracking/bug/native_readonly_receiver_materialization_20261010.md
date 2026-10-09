# Native immutable receiver materialization allocation overhead

Status: MEASURED, OPEN. No semantics-preserving repair is implemented. This evidence does not establish the whole Phase 3 RSS failure cause.

V13 producer SHA256 `3dfd7ed59e04a69eda71879c23ce094a7dee0e15b9fc113828f17f66bacd9ea7` compiled an eight-function fixture with fifty typed local copies per function. Within MIR module lowering, RSS increased 22,948 KiB. Actual linked rt_alloc made 150,700 allocations requesting 11,998,624 bytes; rt_array_copy copied only 4,400 payload bytes. Counter totals overlap and must not be added.

Corrected caller attribution captured 8,288 allocations of 856 bytes (7,094,528 bytes total) across 25 call sites. MirLowering has 107 eight-byte fields. Disassembly confirms local_symbol_slot materializes its immutable receiver in its prologue. Other leading callers include find_local_hir_type, local_is_runtime_array, and is_tagged_text_local. The initial GDB conditional-filter attempt was invalid and is excluded.

Fixed-function and fixed-local-count scale experiments showed approximately linear growth over tested ranges. Built-in heap counters were zero and do not account for these RuntimeValue allocations.

The candidate optimization owner is function parameter lowering, which copies ordinary struct parameters. General struct code generation heap-allocates escaping aggregates. A safe optimization needs conservative proof of no receiver-derived writes, escaping values, address exposure, capture, unknown calls, or alias mutation during execution. Unknown cases must retain existing value semantics. Do not blindly convert fn methods to me or replace all aggregate heap allocation with stack allocation.

Required regressions include scalar query results and allocation reduction; returning/capturing self; callbacks mutating the original while the receiver retains snapshot behavior; nested value-copy isolation; shared class fields; and unchanged mutable/isolated parameter behavior. A measured repair is required before another whole Phase 3 attempt.

Receipts: `/home/ormastes/simple-linux-bootstrap-build-20261009/allocation-probe-20261010/counters.json` and `allocation-caller-probe-corrected-20261010/callers.json`.
