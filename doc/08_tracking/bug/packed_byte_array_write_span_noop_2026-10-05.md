# Packed `[u8]` write_span was a silent no-op; ill-typed `[u8]` stores differ by lane (2026-10-05)

**Status:** write_span: FIXED on branch `work/packed-bytes-parity`.
Ill-typed stores: OPEN, recorded below with the measurements per lane.

## 1. `write_span` on packed `[u8]` (FIXED)

The interpreter stores a `[u8]` in one of two ways: boxed (`[0u8; n]`, one
`Value` per element) or packed (`rt_bytes_alloc(n)` and the other runtime
byte allocators, one byte per element).

`dst.write_span(src, dst_off, src_off, count)` with a packed `dst` did nothing:

- **Local receiver:** the packed identifier path in
  `interpreter_helpers/patterns.rs` had no `write_span` arm. It returned the
  unchanged array as the expression result and wrote nothing.
- **Field, index, or deeper place:** the place kernel declined packed leaves,
  and the self-update tail (`interpreter_method/mod.rs`) re-derived the
  receiver only for `Value::Array`, so the write was dropped.
- **Boxed `dst` with a packed `src`:** this raised
  `write_span expects array source argument`.

Fix: `collections::byte_array_write_span` writes into packed storage using the
same bounds rule and message as the boxed version. If the source span holds an
element that is not `u8`-typed, the destination is widened to boxed values,
which is what a boxed destination would hold. Packed `push` and `insert`
already follow this rule.

It is wired into:
- the packed identifier path
- the place kernel's `WriteSpan` arm
- the self-update tail
- a non-widening `write_span` arm in `handle_byte_array_methods`, so a call
  no longer copies the whole buffer into `Vec<Value>`

`array_write_span` (boxed destination) now accepts a packed source and reads
each byte as a `u8` value.

**Evidence:**
- Spec `test/01_unit/lib/gpu/engine2d/packed_byte_array_write_span_parity_spec.spl`:
  8/8 pass after the fix, 0/8 before. It covers the two reproducers (local,
  field) and six generalizations (overlap, packed source into a boxed
  destination, nested place, zero count, non-`u8` element, aliasing).
- Cargo tests: `cow_alias_mechanism_tests::packed_*` and
  `boxed_destination_accepts_a_packed_source`.

## 2. Ill-typed stores into `[u8]` (OPEN, lanes disagree)

Probe: `test/fixtures/compiler/u8_ill_typed_store_lane_probe.spl` on
`origin/main dd6297cae66`.

| operation | interp boxed | interp packed | JIT | native (`SIMPLE_NATIVE_BUILD_RUST=1`) |
|---|---|---|---|---|
| `a[1] = 300`, read `a[1]` | 300 | 44 | 44 | 44 |
| `a[1] + 255u8` (after the store) | 43 | 43 | 299 | 299 |
| `a.push(5)`, then `last + 255u8` | 4 | 4 | 260 | 260 |
| `a[a.len()] = 1u8` (one past the end) | grows to 6 | grows to 6 | ignored, len 5 | ignored, len 5 |
| `a[a.len() + 2] = 1u8` | grows, `nil` filler | grows, `nil` filler | ignored | ignored |
| packed block | n/a | n/a | **SIGSEGV (rc 139)** after `rt_bytes_alloc` hybrid demotion | runs |

The two interpreter representations agree on everything except the
out-of-range store `a[1] = 300`. There, packed truncates to 44, which matches
the JIT and native lanes; the boxed interpreter is the outlier. The larger
divergences are between the interpreter and the compiled lanes:
- `u8` arithmetic wraps in the interpreter but not in compiled code.
- Writes at or past the end grow the array in the interpreter but are ignored
  in compiled code.
- The JIT crashed on the packed block (fixed, see section 3).

Packed was not changed to deopt on these stores. Deopting would move it away
from the compiled lanes, and it would silently unpack existing
`rt_bytes_alloc` buffers in crypto and font code.

**Unblock condition:** an owner decision on `[u8]` store semantics. Either
truncate in every lane, or make the boxed interpreter path the reference and
change the compiled lanes to match.

## 3. JIT SIGSEGV on a packed `[u8]` (FIXED 2026-10-05, branch `work/jit-bytearray-bridge`)

**Root cause.** The JIT has no native `rt_bytes_alloc`, so the call is spliced
into the interpreter (`hybrid-interp-splice`). The result comes back through
`runtime_bridge::value_to_runtime`. That function had no arm for
`Value::ByteArray` / `Value::FrozenByteArray`, so the value fell through to the
`_ => RuntimeValue::NIL` wildcard. Compiled code then read `a.len() == 0`, and
the next `a[i] = b` stored through NIL and crashed with SIGSEGV (rc 139).

**Fix.** A packed `[u8]` now crosses the bridge as a runtime array of `u8`
values, the same marshalling as a boxed `[u8]`.

**Evidence:**
- Cargo test `runtime_bridge::tests::value_to_runtime_packed_bytes_are_a_real_array_not_nil`.
- Fixture `test/fixtures/compiler/jit_packed_bytes_bridge_probe.spl`: before,
  `len=0` then rc 139; after, `len=4`, `a1=7`, rc 0.
- `u8_ill_typed_store_lane_probe.spl` under the JIT: the packed block now
  prints the same lines as the JIT boxed block and the native lane.
