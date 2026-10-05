# Packed word storage for interpreter arrays (seed) — design

**Status:** DRAFT, for review before implementation. 2026-10-05.

## Problem

The seed interpreter stores every array element as a 64-byte `Value`. A
3840x2160 `[u32]` framebuffer therefore takes **506 MB** where its content
needs 33 MB. Several copies are live at the final composition of the 4K
browser render (software framebuffer, Vulkan readback, snapshot, a COW copy),
so the peak live heap is 3.9 GB.

## What actually sits in the framebuffers (measured)

`build/memprobe/kind_census.spl` classifies each element by its interpreter
kind without a type builtin: `x - x - 1` is -1 for `Int` and wraps for `u32`.

| array | elements |
|---|---|
| `SoftwareBackend.buf` after `init` / `clear` / draws | 100% `UInt{width:32}` |
| `browser_engine_pixels_at` result (64x36) | 100% `Int` |
| `SoftwareBackend.init` allocation `[0; total]` (before the fill loop) | 100% `Int(0)` |
| `_sw_snapshot_buffer` `[0; n]`, then `write_span` of `u32` | `Int(0)`, then `UInt32` |

Two facts shape the design:
- A store-kind-blind packed `u32` vector cannot be exact. Reading an element
  must return the same `Value` kind that was stored: `Int(5)` and `5u32`
  behave differently under arithmetic (`x - 1` with `x = 0`).
- Real framebuffers change kind wholesale. They are created as `Int(0)` and
  then overwritten with `u32`. A packed format that deopts on the first
  mixed-kind write never stays packed long enough to save anything.

## Representation

```rust
/// Exact compact storage for an array whose every element is either
/// `Value::Int(v)` with 0 <= v <= u32::MAX, or `Value::UInt { value: v, width: 32 }`.
struct PackedWords {
    words: Vec<u32>,
    /// 1 bit per element: set = the element is `Value::Int`, clear = `UInt{width:32}`.
    int_kind: Vec<u64>,
}
```

This costs 4 bytes plus 1 bit per element, about 34 MB at 4K instead of 506 MB.
Every read reconstructs exactly the `Value` that was stored. A store that is
not in that domain (negative `Int`, `Int` above `u32::MAX`, any other kind)
**deopts** the array to boxed values in O(n) and then performs the store.
After that the array behaves exactly like a boxed one, because it is one.

## Where it lives: inside `Value::Array`, not a new variant

The packed `[u8]` precedent (`Value::ByteArray`, a separate variant) shows the
failure mode of a new variant. Every `match` that does not know the variant
falls through `_ =>` and silently does something else. `write_span` was a
no-op for exactly that reason (`doc/08_tracking/bug/packed_byte_array_write_span_noop_2026-10-05.md`).

Instead, the payload of the existing variant changes:

```rust
Value::Array(Arc<ArrayData>)

struct ArrayData {
    packed: Option<PackedWords>,
    /// Materialized boxed view; filled on first boxed access.
    boxed: OnceLock<Vec<Value>>,
}

impl Deref for ArrayData { type Target = Vec<Value>; /* materialize once */ }
impl DerefMut for ArrayData { /* materialize, then drop `packed` (deopt) */ }
```

**Correctness by construction:**
- Every existing site keeps compiling through `Deref`/`DerefMut` and gets
  exact boxed semantics. A read-only site that is not migrated materializes
  the boxed view once: correct, at the old memory cost.
- Any `&mut` access deopts permanently, so packed and boxed state can never
  disagree.
- Sites that construct `Value::Array(Arc::new(vec))` stop compiling until
  they write `ArrayData::from(vec)`. The compiler points at every one; none
  can be missed silently.

**Coexistence invariant (the one correctness rule).** Materializing the boxed
view is itself a deopt. If `boxed` is set, `packed` is ignored, and every
packed-aware method checks `boxed.get().is_none()` before it touches `words`.
Otherwise the call goes through the boxed view. `Clone`, `set` and
`Arc::make_mut` drop `packed` once `boxed` exists. A write therefore never
reaches only one of the two representations. Each materialization is counted
(`ARRAY_MATERIALIZE`).

**Method dispatch is the choke point.** `evaluate_method_call` passes
`&[Value]` to `handle_array_methods`. Through `Deref`, any method call would
materialize the whole array, including the `self.buf.len()` that
`_span_safe_count` makes on every scanline. That is the same failure as the
2.4-billion-allocation `handle_byte_array_methods` incident. `len`,
`is_empty` and `write_span` are answered before that call, as the byte-array
metadata fast path already does.

**Memory and speed** come only from explicitly migrated hot paths:

| hot path | packed-aware API |
|---|---|
| `xs[i]` read: expression, place, field | `get(i) -> Option<Value>` |
| `xs[i] = v`: identifier, field (ClassInstance/Object), place kernel | `set(i, v)` (deopts outside the domain) |
| `len`, `is_empty` | `len()` |
| `write_span` (all paths), `_sw_snapshot_buffer` | word copy when the source is packed or all in-domain |
| `[x; n]` repeat with `x` in the domain and `n >= 256` | creates packed |
| `for x in xs` | `iter_values()` (no materialization) |
| `==` and `{xs}` interpolation | element-wise without materialization |
| extern marshalling of `[u32]` / `[i32]` (`rt_engine2d_*`, Vulkan upload) | `as_u32_slice()` when every kind matches |

`PartialEq`, `Debug` and `Clone` for `ArrayData` are written by hand so they
equal the boxed results.

## Risks and how each is checked

1. **A missed hot path makes a 506 MB boxed view appear.** Correct, but no
   memory win. Detection: a `SIMPLE_MEM_TRACE` counter `ARRAY_MATERIALIZE`
   with element counts. Gate: the 4K run must show no materialization of the
   framebuffers.
2. **`OnceLock` plus `Arc::make_mut`.** A materialized view must be dropped
   together with `packed` on mutation. `DerefMut` sets `packed = None` before
   returning `&mut Vec<Value>`.
3. **Behavior parity.** A boxed-vs-packed differential spec covers every arm
   of `handle_array_methods`, index read/write in all place shapes, slices,
   `for`, equality across representations, interpolation, `freeze`,
   dict-key use, push/grow/pop/insert/remove, aliasing/COW and extern calls.
   It runs in interpreter mode and must give line-identical output.
4. **Cross-crate users of `Value::Array`.** About 145 files and 547 lines
   reference the variant. Most compile unchanged through `Deref`; the rest
   are compile errors, not silent changes.

## Delivery plan

Named hot frames, from the 4K measurements:
- `read_pixels_region`: `self.buf[row_base + x]` reads.
- `sw_set_pixel`: `self.buf[idx] = color`, through the `Object` case-2 path
  and the `ClassInstance` `field_mut` path.
- `_sw_snapshot_buffer`: `[0; n]` followed by `write_span`.
- The software `init` allocation `[0; total]`.

| PR | content | gate | expected 4K change |
|---|---|---|---|
| 1 | `ArrayData` with `Deref`/`DerefMut`, boxed only (no `PackedWords` yet), all constructors migrated | identical cargo failure set; identical spec counts; identical 64x36 pixel hash (same tree, binary toggled) | none; pure type refactor |
| 2 | `PackedWords`, `[x; n]` producer, index get/set in every place shape, `len` / `is_empty` / `write_span` intercepted before method dispatch, iteration, equality, display | differential spec line-identical; cargo; pixel hashes; **zero framebuffer-sized materializations in a 4K run** | the software framebuffer only, about 0.5 GB of the 3.9 GB live peak |
| 3 | `array_from_u32(&[u32])` at extern-return marshalling (Vulkan readback, `rt_engine2d_*`), packed→packed `write_span`, `[u32]` extern argument views | 4K footprint, materialization counter, pixel hash | readback, snapshot and COW copies: the bulk of the remaining peak |

**Known exclusion:** an `[i32]` or `Int` array holding negative values does not
pack; it deopts on the first negative store. The blur accumulators are
non-negative and do pack; coordinate arrays with negatives do not. This is
expected behavior, not a bug.

PR 1 is a pure type refactor and can land independently. Each later PR is
reversible by turning packing off in the producer.
