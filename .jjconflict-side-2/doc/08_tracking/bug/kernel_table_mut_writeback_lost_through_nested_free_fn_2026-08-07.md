# CpuKernelTable `mut` write-back lost through nested free fn / self.field (interpreter)

- **Date:** 2026-08-07
- **Status:** Open (compiler/interpreter defect); production code restructured to avoid the shape
- **Found during:** T10 (extend the honest per-bucket SIMD gate beyond fill_const)
- **Family:** sibling of `self_pass_to_free_fn_mutation_loss_2026-05-29.md`

## Symptom

`kernel_table_register(t, ...)` called DIRECTLY from a spec body persists
(`kernel_table_lookup` sees the slot). The SAME call routed through an
intermediate free fn taking `mut table: CpuKernelTable` does not — the
caller's table is unchanged. Also lost: registrations applied to
`self.kernel_table` by a `me` method passing the field to the free fn.

Verified 2026-08-07 under `bin/simple test` (tree-walk interpreter, seed
binary `bin/release/x86_64-unknown-linux-gnu/simple`):

- one hop, spec var -> `kernel_table_register(t, ...)`: lookup = provider (persists)
- two hops, spec var -> probe(`mut table`) -> register: lookup = scalar (LOST)
- `me` method -> `kernel_table_register(self.kernel_table, ...)`: LOST
  (caught by the "owned-table persistence" example in
  `backend_software_kernel_table_bucket_spec.spl` while it exercised this shape)

Array (`[u32]`) mut params do NOT show the loss (e.g. `_scalar_fill_row(self.buf, ...)`
works); the loss reproduces with the struct/class `CpuKernelTable`.

## Impact before the fix

`ensure_kernel_table()` in
`src/lib/gc_async_mut/gpu/engine2d/backend_software.spl` threaded
`self.kernel_table` through `_kernel_probe_fill_bucket` (two hops), so ALL
registrations were silently dropped and the production table was
unconditionally all-scalar regardless of measurement — unobserved because
fill_const lost its timing gate on this host anyway.

## Workaround now in production

Probes measure only and return a verdict bitmask; `ensure_kernel_table()`
registers into a LOCAL table (one hop, persists), seals it, and
field-assigns it to `self.kernel_table`. Guarded by the
"builds the full 16-slot-probed table ... persists it observably" example
(asserts `backend.kernel_table.sealed == true` after the first fill).

## Unblock condition

Fix interpreter `mut` parameter write-back for struct/class values when the
parameter is re-passed to another `mut` parameter, and when a `self.field`
is passed to a free fn; then the local-table indirection can be removed.
