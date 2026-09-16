# CpuKernelTable `mut` write-back lost through nested free fn / self.field (interpreter)

- **Date:** 2026-08-07
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Found during:** T10 (extend the honest per-bucket SIMD gate beyond fill_const)
- **Family:** sibling of `self_pass_to_free_fn_mutation_loss_2026-05-29.md`

## 2026-08-17 (lane w02/s6a) — GREEN ONLY BECAUSE OF A LOAD-BEARING WORKAROUND

Classified by CONTENT. `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl`
still carries the workaround **in source, as executable structure, not prose**:

- `:75-76` — header note: "CpuKernelTable passed caller -> probe ->
  kernel_table_register loses the register's write-back at the intermediate hop
  under the interpreter".
- `:1310-1318` — the live comment on the registration path: "a mut table
  threaded through a probe loses `kernel_table_register`'s write-back, and so
  does registering into `self.kernel_table` directly (self.field passed to a
  free fn)... A local var -> free fn register is the one shape that persists;
  the sealed local is then stored with a plain field assignment." The code
  literally does `var table = kernel_table_new()` and assigns at the end.
- `:1404` — the same shape again for the framebuffer: "passing `self.buf`
  directly hands the executor a field-read COPY under the interpreter... which
  left the SIMD lane's fills invisible", worked around with `var work_buf = self.buf`.

So this row is **live, not stale**. The suite is green because the stdlib was
restructured around the defect; the defect itself is untouched. **Note this is
NOT the COW write-back family** that BRIEF correction #2 declares already fixed
via `merge_shared_collection_fields` — that function propagates Array/Dict/
ByteArray *fields* and deliberately keeps nested structs value-typed, which is
exactly the case that still loses `CpuKernelTable` (a struct with a `[i64]`
inside, passed as `mut` through an intermediate frame). Do not close this row on
correction #2.

**Out of scope for this lane.** The root cause is in the Rust interpreter's
argument write-back, not in `src/lib/**`; this lane may only edit
`src/lib/gc_async_mut/**` and `src/lib/nogc_async_mut/**`, so no fix was
attempted. Removing the workaround to demonstrate RED would be a live
regression to the SIMD backend and was deliberately not done.

**Not proven:** no execution evidence. An unworked-around reproducer was written
(`shape7` in the lane's `probe_a.spl`: `Holder.fill_via_self_field()` vs
`fill_via_local()`, both through a nested `mut` free fn) but never ran — all six
`scripts/resource/test-slot.shs` slots were held for the entire session by
parallel sessions running ~173 concurrent `bin/simple test` processes outside
the cap. The probe is the ready-made reproducer for whoever picks this up.

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

## Triage 2026-08-17 (lane m7c_lib_async) — ALREADY FIXED IN SOURCE

The interpreter now has the container write-back this doc was missing:
`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:975`
defines `fn merge_shared_collection_fields(caller_val: &mut Value, callee_val: &Value)`,
recursing at :1000 and invoked from the argument write-back path at :1140
(with an explanatory comment at :1137). It propagates Array/Dict/ByteArray
fields from callee back to caller while deliberately leaving scalars and nested
structs value-typed — precisely the "mut write-back lost through a nested free
fn / self.field" shape recorded here.

Caveat, stated rather than glossed: this is a **Rust** change, so the currently
deployed `bin/simple` (a bootstrap seed) does not necessarily contain it. The
fix is confirmed present in SOURCE by content; it was **not** re-confirmed by
execution against a binary built from that source. Treat as
already-fixed-pending-rebuild-verification, not as executed-green.

The production restructure in `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl`
was left in place — it is correct code either way, and unwinding it is not this
lane's call.
