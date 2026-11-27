# Seed JIT: assigning a local array to a class field aliases it (interpreter copies)

- **Filed:** 2026-11-04 (u8param lane)
- **Status:** FIXED in seed source (jitalias lane, 2026-11-04); seed redeploy is the bootstrap lane's.
- **Platform:** aarch64-apple-darwin, seed built from `release/1.0.0` (includes `bafc15f38a7`)

## Repro

```simple
class Hold:
    buf: [u32]
    me poke():
        self.buf[0] = 9u32
fn main():
    var a: [u32] = [1u32, 2u32]
    var h = Hold(buf: [])
    h.buf = a
    h.poke()
    print "a0={a[0]} h0={h.buf[0]}"
main()
```

| mode | output |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpreter simple run` | `a0=1 h0=9` |
| `simple run` (JIT) | `a0=9 h0=9` |

Local-to-local `var b = a` copies in both modes (`a0=1 b0=9`), so only the
field-store path aliases.

## Impact

`backend_vulkan_font.spl` packed single-submit oracle: `oracle.buf = oracle_before`
then `oracle.draw_image_blend(...)` mutates `oracle_before` under JIT, so
`readback_nonblank_pixels` is 0 and Vulkan font promotion never succeeds under
`simple run` (see `macos_vulkan_2d_vector_font_empty_batch_native_fault_2026-07-26.md`,
2026-11-04 section).

## Fix direction

JIT lowering of a field store of an array value must give the field its own
copy-on-write handle (match the interpreter), rather than the Simple source
adding a defensive `.clone()`.

## 2026-11-04 resolution (jitalias lane)

Root cause: `HirStmt::Assign` with a `FieldAccess` target
(`src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs`) only snapshotted
declared `struct` values (`copy_if_value_type`); an array PLACE went straight
into `FieldSet`, storing the source's `rt_array` handle. The `var c = arr` Let
arm already emitted `rt_array_copy` for array places (bug
seed_array_local_alias_cow_bypass_2026-07-17). The field-store arm now applies
the same rule: array place -> `rt_array_copy`; fresh literal / call result
transfers directly.

Evidence (seed built from this worktree, `cargo build --release --bin simple`):

| check | deployed seed | fixed seed |
|---|---|---|
| repro, JIT | `a0=9 h0=9` | `a0=1 h0=9` |
| repro, interpreter | `a0=1 h0=9` | `a0=1 h0=9` |
| `test/01_unit/compiler/interpreter/field_array_assign_value_semantics_spec.spl` (`simple run` and `simple test`) | — | 5/5, 5/5 |
| `cargo test --release -p simple-compiler --test jit_field_array_assign_value_semantics` | — | 3/3 |
| `--test jit_struct_array_field_leak` (no regression) | — | 5/5 |

`native_gpu_font_readback_spec.spl` under `simple run` with the fixed seed:
5/8 pass. Note the spec does NOT run on the JIT at all: the JIT compile fails
with `HIR lowering error: Cannot infer field type: struct 'Void' field 'ready'`
and falls back to the interpreter. Engine2D font promotion reports no failure
reason (`Engine2D=` empty); the 3 failures are Engine3D
`public-vulkan-font-install-failed`, missing retained SimpleOS QEMU
`evidence.env`, and the latency/budget example. So the JIT-side Engine2D
CPU-oracle path is still not exercised by this spec until that HIR error is fixed.

Known tradeoff: field stores of array places now always copy; the JIT lane has
no release for the replaced field buffer, so `st.buf = o` in a hot loop retains
one copy per iteration (same class as the leak `array_move.rs` addresses for
Let). Not extended to field stores here.

Not same root, not fixed: module-level `var` passed to a `mut` array param is
not written back in either engine (see
`seed_interp_mut_u8_array_param_element_write_lost_2026-11-04.md`).

## 2026-11-04 follow-ups (jitvoid lane)

- The `struct 'Void' field 'ready'` HIR error is fixed:
  `seed_jit_nullable_receiver_method_typed_by_shorter_owner_2026-11-04.md`.
  Engine2D CPU-oracle path under the real JIT (collector wrapped in `main`):
  `status=pass cpu_oracle_parity=true`.
- The per-iteration copy retention from the field-store copy is fixed for dead
  sources: `seed_jit_field_store_array_copy_never_freed_2026-11-04.md`
  (400k iterations 168 MB -> 98 MB RSS).
