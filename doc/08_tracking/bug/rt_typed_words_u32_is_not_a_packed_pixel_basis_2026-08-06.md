# `rt_typed_words_u32_*` is NOT a packed pixel basis — 8-byte stride, same as `[u32]`

- **Filed:** 2026-08-06
- **Status:** Finding (premise refuted); no code built on it
- **Component:** runtime — core array storage / pixel representation
- **Lane:** F2b, which was chartered to build a packed pixel surface on this basis

## Verdict

**The premise is refuted.** `rt_typed_words_u32_*` was named (in
`doc/09_report/render_pipeline_profile_2026-08-06.md`, and echoed into the
`packed_span.spl` header) as the credible densely-packed 4-byte-stride
alternative to `[u32]`. It is not. It is an **8-byte-stride** accessor that
masks its result to 32 bits — the *same storage width* as `[u32]`.

Building a zero-copy pixel surface on it would have produced a buffer that is
still 2x the memory of true ARGB32 and still unconsumable by any SIMD kernel
expecting packed 32-bit pixels. **No surface was built.** Per the lane's own
stop condition, the verification result is the deliverable.

## Evidence — the two runtimes agree independently

**C runtime** (`src/runtime/runtime_native.c`):

- `:5927` — `rt_typed_words_u32_at` reads `((int64_t*)array->data)[idx]`.
  The cast is `int64_t*`. Stride is 8.
- `:5780` — `rt_core_array_reserve`:
  `elem_size = (flags & RT_CORE_ARRAY_FLAG_BYTES) ? sizeof(uint8_t) : sizeof(int64_t);`
  **Element size is binary: 1 or 8. There is no 4-byte element size anywhere in
  this array runtime.**
- `:806-814` — `RtCoreArray` holds an untyped `void* data`; width comes solely
  from the flag above.

**Pure-Simple runtime** (`src/runtime/simple_core/core_array_ops.spl`), reached
independently:

- `:382` — `rt_typed_words_u32_at` → `spl_load_i64(array_items(array), actual_idx * 8)`.
  The `* 8` is hardcoded.
- `:386`, `:389`, `:399` — `_unchecked`, `_data_at`, `_push_known_at` all use the
  same `idx * 8`.

Both implementations independently hardcode an 8-byte stride, so this is not a
backend quirk — it is the storage contract.

**Third confirmation, from a consumer that already pays the cost.** The ROCm
GPU backend (`src/runtime/runtime_rocm.c`) cannot hand typed words to the
device. It allocates a real `uint32_t` array and copies element-by-element in
both directions:

- `:507` — `copy[i] = (uint32_t)rt_typed_words_u32_at(pixels, i);`  (gather)
- `:539` — `rt_typed_words_u32_set(pixels, i, copy[i]);`            (scatter)

That is the *same* gather/scatter the render plan identified around the SIMD
kernels, appearing independently in the GPU path — because both are compensating
for the same representation gap. It is the strongest available evidence that the
conversion is intrinsic to typed words rather than incidental to one call site.
Sanity check on the negative: `sizeof(uint32_t)` appears in `runtime_native.c`
only inside a `malloc` for exactly this kind of temporary copy (`:4319`), never
as an array element size.

A whole-repo grep (994 hits) surfaced no other storage implementation: outside
the two runtimes above, every hit is a call site, a MIR-lowering reference, a
Rust seed path (out of scope by policy), or a build artifact.

## What *is* true from the original claim

The claim had two halves; only one survives.

| claim | verdict |
|---|---|
| values are tagged | **TRUE, but avoidable.** `RT_CORE_ARRAY_FLAG_U64_PACKED` (`:116`) makes stores raw and reads skip `rt_core_numeric_arg`. Constructor exists: `rt_array_new_with_cap_u64` (`:5148`). |
| 4-byte dense stride | **FALSE.** Always 8 bytes, flag or no flag. The flag controls *tagging*, never *width*. |

So `rt_typed_words_u32` + the packed flag gets you *untagged* 32-bit values at
8 bytes each. That is strictly better than `[u32]` for arithmetic, and still
useless as a pixel buffer handed to a kernel.

## The actual packed basis

A **BYTES-flagged array** — `elem_size = sizeof(uint8_t)`, densely packed:

- Constructor: `rt_byte_array_new(cap)` → `rt_core_array_new(cap, RT_CORE_ARRAY_FLAG_BYTES)`
  (`runtime_native.c:5431`).
- Pixel accessors already exist: `rt_typed_bytes_u32_le_at` /
  `rt_typed_bytes_u32_le_set` (`runtime.h:457,460`) — read/write a 32-bit
  little-endian pixel at a byte offset.

That is 4 bytes per pixel, contiguous, and is the layout a C SIMD kernel or a
plain `memcpy`/blend can consume with no conversion. **This, not typed words, is
where a packed pixel surface should be built.** It was not built here: the lane
was chartered against a specific basis, that basis failed verification, and
silently substituting a different one would have put unreviewed foundations
under the next lane.

## Consequence for already-landed work

`src/lib/common/memory/packed_span.spl`'s header (landed `55b639ff236`) says
"The credible packed basis is `rt_typed_words_u32_*`, not `[u32]`." **That
sentence is wrong** and should be corrected to name the bytes-array basis. The
rest of that header — that `[u32]` is 8-byte-strided and `<<3`-tagged, and that
the SIMD gather/scatter is a representation conversion — is unaffected and
still holds. The module's validation logic is untouched by this finding.

The `packed_span.spl` correction was NOT made here: that file is owned by
another lane. Exact change wanted, for its owner:

> Replace "The credible packed basis is `rt_typed_words_u32_*`" with a
> reference to a `RT_CORE_ARRAY_FLAG_BYTES` array accessed via
> `rt_typed_bytes_u32_le_at/set`, and note that `rt_typed_words_u32_*` is
> 8-byte-strided and therefore not a candidate.

## Handoff — wiring not done

`backend_software.spl`, `simd_kernels.spl` and `simd_native_rows.spl` were
off-limits to this lane and are untouched. The wiring a follow-up should do,
once a bytes-backed surface exists:

1. Back the software backend's pixel store with `rt_byte_array_new(w * h * 4)`.
2. Replace per-pixel `[u32]` reads/writes with
   `rt_typed_bytes_u32_le_at/set(buf, (y * w + x) * 4)`.
3. Only then is `simd_native_rows.spl`'s per-row FFI round trip removable —
   the extern can take the byte array's base directly instead of building and
   returning a fresh `[u32]` per row (`backend_software.spl:615`).

Step 3 is the entire point; steps 1-2 are prerequisites, and none of them are
possible on typed words.

## Not verified here

- Whether `rt_typed_bytes_u32_le_*` is reachable from ordinary `.spl` code
  today (it is declared in `runtime.h`; no Simple-level wrapper was found in
  `core_array_ops.spl` by grep). A wrapper may need adding.
- No benchmark was run. The lane's benchmark step was conditional on the basis
  verifying, and it did not.
