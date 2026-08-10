# Spec helpers that take a struct BY VALUE and mutate it — third vacuity family

- **ID:** spec_value_type_helper_mutates_copy_family_2026-08-10
- **Status:** PARTIALLY FIXED (2 specs fixed; 3 left RED, see below)
- **Found by:** sweep following `6f8f3230db4` (dbfs BTree delete spec)
- **Binary:** `src/compiler_rust/target/bootstrap/simple` (33,653,056 bytes, mtime 2026-08-09 23:10)

## Mechanism

A `struct` in Simple is a VALUE TYPE. A spec helper declared

```
fn mutate(x: SomeStruct, ...):
    x.field.push(...)      # or x.field = ...  / x.data[i] = ...
```

mutates a COPY. The caller's `var` is never modified, so the operation is a
silent no-op.

This is a third distinct vacuity family, after non-matcher `expect` tails and
comment-matching needles. **Both existing gates are blind to it.** The
signature failure mode is asymmetric: blocks asserting only POSITIVE PRESENCE
stay green (a no-op trivially satisfies them); only ABSENCE / NEGATIVE
assertions (`to_equal(false)`, `to_not_equal`, "was removed", "differs") go red.
So a spec can be mostly green and still be asserting nothing.

`class` types are references and are NOT affected.

## Census (scan roots: `test/`, all trees)

Scanner: helpers `fn f(p: <UpperType>, ...)` whose body mutates `p`,
`p.field`, or `p.field[i]`. 25 helper sites in 21 files; after filtering to
`struct` (value) receivers:

| spec (both trees) | struct | verdict before | assessment |
|---|---|---|---|
| `test/03_system/engine/physics_perf_spec.spl` + `test/system/…` | `DynamicBvh2D` | 0/4 — ALL RED | real trap, FIXED (inlined) |
| `test/05_perf/graphics_2d/report_spec.spl` + `test/perf/…` | `TFB` (spec-local) | 17/18 — 1 RED | real trap, 17 blocks VACUOUS, FIXED (`struct`→`class`) |
| `test/01_unit/lib/service/lease_grant_spec.spl` + `test/unit/…` | `LeaseManager` (spec-local) | 4/10 — 6 RED | real trap, LEFT RED (see below) |
| `test/01_unit/lib/service/request_queue_spec.spl` + `test/unit/…` | `RequestQueue` (spec-local) | 2/8 — 6 RED | real trap, LEFT RED (see below) |
| `test/01_unit/app/sj/busy_contract_spec.spl` + `test/unit/…` | `LeaseManager` (spec-local) | not run | same shape, suspect |
| `test/01_unit/compiler/interpreter/self_field_assign_spec.spl` + twin | `MutableStructDictHolder` | — | INTENTIONAL: the spec exists to characterise this exact semantics |

Not affected (receiver is a `class`, i.e. a reference): `CrsCell`,
`T32JobManager`, `RecordingRenderBackend3D`, `HostCompositor`, `Engine2D`,
`DynamicBvh2D` call sites in `draw_backend_matrix_spec`, `Game`, `Canvas`,
`SbiMock`, `HostedBrowserRendererRegistry`.

`test/02_integration/storage/dbfs/**` and `test/integration/storage/dbfs/**`:
clean after `6f8f3230db4`.

## Fixed

- `physics_perf_spec.spl` (both trees) — `insert_grid` / `insert_cluster`
  removed; insertion loops issued inline on the caller's `var bvh`. Comment
  recording the trap added.
- `report_spec.spl` (both trees) — `TFB` changed from `struct` to `class`.
  Every painter (`tclear`, `trect`, `tiny_fill`, `tiny_blit`, `tiny_scroll`)
  takes the framebuffer as a parameter and mutates it, so with a value type
  every scene hashed the same all-zero buffer. Only
  "different scenes produce different pixel hashes" (a `to_not_equal`) caught
  it; the other 17 blocks were vacuous.

## Left RED (real defects — do not weaken)

`lease_grant_spec.spl` (4/10) and `request_queue_spec.spl` (2/8) are red for
this reason, but they have a SECOND, deeper defect that must be fixed first:
**each spec re-declares its own local `struct LeaseManager` / `struct
RequestQueue` and reimplements the acquire/release/enqueue/dequeue logic
inside the spec file**, so it never exercises
`src/lib/nogc_sync_mut/service/lease_manager.spl` or
`.../request_queue.spl` at all. Making the local reimplementation mutate
correctly would produce a green spec that still tests nothing in `src/`.

Observed failures (value-type no-op signature — the manager never records a
lease, so every BUSY / uniqueness / release assertion collapses):

```
✗ rejects second exclusive lease while first is held   expected  to contain BUSY
✗ grants exclusive after release                       expected false to equal true
✗ generates unique lease IDs                           expected true to equal false
✗ rejects shared lease while exclusive is held         expected  to contain BUSY
✗ rejects exclusive while shared is held               expected true to equal false
✗ BUSY message contains text                           expected  to contain BUSY
```

Unblock condition: rewrite both specs (and `busy_contract_spec.spl`) to import
the real library types instead of re-declaring them, then issue the operations
inline on the caller's `var`.

## Gate gap

Neither the non-matcher-`expect` gate nor the comment-needle gate detects this.
A future gate should flag: a spec-file `fn` whose parameter type resolves to a
`struct` and whose body mutates that parameter (field assign, field-method
mutation, or element store).
