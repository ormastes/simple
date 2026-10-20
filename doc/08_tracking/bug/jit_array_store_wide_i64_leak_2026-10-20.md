# JIT: storing a full-width i64 into an array allocates and is never freed

- Date: 2026-10-20
- Status: fixed for statically typed `[i64]` (seed JIT + Rust runtime); dynamic/`any` arrays remain a named gap, see Resolution
- Found by: pure-Simple SHA-512 work (`src/lib/common/crypto/sha512.spl`)
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed), default JIT mode

## Symptom

Under the JIT, each store of an i64 whose value is outside the tagged-int
range into an `[i64]` array grows RSS by about 48 bytes, and the memory is not
reclaimed. Locals holding the same values do not grow. The interpreter does
not show it.

Reproducer (4,000,000 stores into an 80-element array):

```
fn main():
    var w: [i64] = [0; 80]
    var x: i64 = BASE
    var n = 0
    while n < 4000000:
        x = x + 1
        w[n & 63] = x
        n = n + 1
    print "{w[3]}"
main()
```

| BASE | wall | max RSS |
|------|------|---------|
| 5 | 0.17 s | 33 MB |
| 8070450532247928832 | 1.09 s | 221 MB |

The same loop with the value kept in a local and no array store stays at
33 MB for both values.

## Impact

A first SHA-512 rewrite with the message schedule in an 80-word array reached
428 MB RSS for PBKDF2-HMAC-SHA-512 at c=80000 under the JIT (compression
alone: 40 MB at 2,000 calls, 127 MB at 40,000). The shipped version keeps the schedule and
working variables in locals, so its RSS stays flat (125 MB at c=80000, the
same as at c=4096). Any other 64-bit hash, cipher or bigint code that keeps
full-width words in arrays still pays this cost.

## Related

- `[u64]` element reads shift arithmetically in the interpreter
  (`(u[0] >> 60) as i64` gives -1 for `u[0] = 2^64-1`, JIT gives 15). This is
  why the SHA-512 code stores no state in `[u64]` arrays.

## Resolution (2026-10-20, work/jit-wide-i64-array-leak)

Cause: `w[i] = x` lowered to `BoxInt` -> `rt_value_int` -> `RuntimeValue::from_int`,
which heap-boxes anything outside the 61-bit inline range. Nothing frees the box
(no refcount, no collector; `RuntimeValue` is `Copy`, so the old slot value may be
aliased and cannot be released on overwrite).

Fix: a typed `[i64]` lane (`rt_typed_words_i64_at/_set/_push`). The first value
outside the inline range packs the tagged array in place to raw i64 words
(`gc_flags::LAZY_WORDS | U64_PACKED`, same buffer); later wide stores write the
word, no allocation. Arrays that only ever hold narrow values never change layout.
Any consumer that does not understand the packed layout unpacks automatically
(`get_typed_ptr`); packed-aware ones opt out. Raw words are host-endian-free: no
byte view of the buffer is taken anywhere (the words are read/written as i64).

Measured (same base commit dacf1e81637, aarch64, JIT, loaded host):

| program | before | after |
|---|---|---|
| leak reproducer above (4M stores) | 0.86 s, 229.5 MB | 0.03-0.06 s, 40.1 MB |
| 80-word-schedule SHA-512, 100k compressions | 1.8-2.1 s, 391 MB | 0.25-0.29 s, 42.4 MB |
| tight `[i64]` loop, 12.3M read+write | 0.14-0.16 s user | 0.11 s user, 38 MB (was 38.6) |
| probe `jit_wide_i64_array_store_jit_probe.spl` (1M overwrite + 1M append) | FAIL, 139.5 MB | PASS, 59.6 MB |

Thread safety: the runtime has no ownership or refcount information, so in-place pack/unpack is only allowed before user threads exist. Every spawn entry point (`rt_thread_spawn_*`, `rt_actor_spawn`, `rt_async_spawn*`, `rt_par_launch`, the future worker pool, `spawn_actor`) calls `note_user_threads_started()`, which unpacks every live packed array and permanently disables packing; after that the lane stores tagged (one box per wide store, the old behaviour). The C pthread/pool runtime reaches the same switch through the weak `simple_note_user_threads_started`. Any use of threads, actors, async or parallel launch anywhere in the process turns packing off for the rest of the run (one box per wide store again). Tests: `spawn_entry_points_switch_packing_off`, `starting_user_threads_unpacks_every_packed_array_and_stops_packing`.

Named gaps (not fixed here):
- Arrays whose static element type is erased (`[any]`, generic `[T]`, dict values)
  still box wide values per store; releasing on overwrite is unsafe without
  ownership (aliases are the norm). Needs a collector or refcounts.
- Freestanding (baremetal) and WASM targets keep the old path; the C runtime
  twin (`runtime_native.c`) implements the lane without in-place packing.
- A generic read of a packed wide element (`rt_array_get`, erased receivers) re-boxes it (scope-tracked); An array unpacked once is never re-packed (bounds the worst case at the old one-box-per-store).
- Sorting a TAGGED array holding wide boxes is still wrong (filed: `doc/08_tracking/bug/sort_tagged_array_with_wide_int_boxes_unsorted_2026-10-20.md`) (packed arrays sort
  correctly, signed).
- `[u64]` element reads still shift arithmetically in the interpreter (separate).
