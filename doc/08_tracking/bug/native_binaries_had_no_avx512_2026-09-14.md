# Native binaries had ZERO AVX-512 — the DB and web servers were AVX2 at best

- **Status:** root cause found and fixed for one kernel; the same fix is owed to
  the rest. Two further defects found on the way and filed below.
- **Found:** 2026-09-14, while trying to substantiate "the DB server and web
  server are automatically AVX-512 optimized".

## The measurement nobody had taken

Every AVX-512 claim in this tree was verified against the **Rust seed**, which
is the interpreter. A `native-build` binary links the **C runtime** instead.
Disassembled, before any change:

    native binary: 106 ymm, 0 zmm

So a shipped Simple binary — the DB server, the web server — got AVX2 and
nothing wider. The nine kernels the disassembly gate certifies are the Rust
ones; the gate reads the seed, not a product binary.

## Root cause: the duplicate-body-under-target-attribute idiom is clang-only

Every SIMD kernel here is the same source loop re-emitted under
`#[target_feature]` / `__attribute__((target(...)))`, trusting the compiler to
widen it. Measured on identical source:

| compiler | zmm emitted |
|---|---|
| clang | 13 |
| gcc (MinGW-W64 16.2.0) | **0**, and no distinct symbol at all |

GCC folds the identical bodies together and compiles the survivor for the
baseline target. `-mprefer-vector-width=512` does not change it. The native
link on this host is gcc, so the idiom bought exactly zero AVX-512 in a product
binary while the Rust twin's 512-bit code made it look covered.

**Fixed by writing the lanes explicitly** for `rt_db_bitmap_and_u32`. The
transform is exact, not approximate: box/unbox are `p << 3` and
`(uint32_t)(v >> 3)`, and `(a >> 3) & (b >> 3) == (a & b) >> 3` for logical
shifts, so

    o = ((((l & r) >> 3) & 0xFFFFFFFF) << 3)

is bit-identical to the scalar body. Verified by a standalone harness over
every length 0..128 plus saturating bit patterns, on both compilers:
**9408 comparisons, 0 mismatches**.

After the fix, a real native binary contains **7 zmm** (gcc; clang 28 at object
level). That is the first AVX-512 in a shipped Simple binary.

## The `rt_env_vars` blocker was never about `rt_env_vars`

`native-build` failed with `unknown extern function: rt_env_vars`, and that was
treated as an unbacked extern for weeks. It is registered
(`interpreter_extern/mod.rs:1328`). The real cause: the pure-Simple native
driver spawns a **worker** and the worker it spawns is the deployed
`bin/simple.exe` — dated Sep 7, 16 MB, against a current build of 71 MB. The
stale worker lacks the registration.

`SIMPLE_NATIVE_BUILD_RUST=1` takes the Rust handler directly, spawns no worker,
and builds clean. Every "native-build is blocked" note in this tree should be
re-read in that light before being believed.

## Still open — and it limits what the fix above buys

`rt_db_bitmap_and_u32` returns an EMPTY array in a native binary, so the Simple
caller sees "not backed" and falls back to scalar. The AVX-512 code is now in
the binary but is not reached through `accel.spl`.

It is specific to that kernel, not general FFI breakage, which is what makes it
worth chasing rather than assuming:

  * `rt_simd_has_avx2()` -> true and `rt_x86_avx512_os_state_usable()` -> true
    natively, so CPU probes marshal fine;
  * `rt_engine2d_blend_const_span_pct_u32` works natively AND is correct —
    black blended 50% with white returns `0xFF7F7F7F`, not the input;
  * `db_bitmap_span` is sound for the inputs used (limit 4, len 4), and
    `rt_array_new_uninit` is defined in the binary and was not one of the 23
    generated stubs.

The difference between the two is that the working kernel writes IN PLACE and
returns `dst`, while the failing one ALLOCATES a result. That is the next thing
to test, and note the trap it implies: an in-place kernel's failure path
returns its input, so a length check alone cannot tell success from failure —
the blend above had to be checked by CONTENT.

## What this means for the goal

"The DB server and web server are automatically AVX-512 optimized" was not true
and is not yet true. What is now true: the toolchain-level blocker is
understood and fixed for one kernel with exact-parity evidence, native-build
works, and the remaining gap is a specific, named allocation defect rather than
an unknown.

## Resolved — all three native defects, with a gate

The "still open" section above named one symptom (`rt_db_bitmap_and_u32`
returning empty) and one hypothesis (in-place kernels work, allocating ones
fail). The hypothesis was right and the cause was more general than the DB.

**Defect 2 — `rt_array_new_uninit` never set `len`.** It calls
`rt_core_array_new_fill`, which sets `cap` and leaves `len` at the calloc zero.
So every kernel that allocates n, fills n and returns handed back an array with
**correct data and a length of zero**. `rt_array_repeat` already set `len` by
hand after the same call; nothing else did. All 7 callers are span kernels that
want `len == cap`, so the constructor now sets it — the name means "n elements,
values uninitialized".

Measured across every allocating extern, before and after:

    mask_span   len=0 -> 4
    bitmap_and  len=0 -> 4
    bitmap_and (limit=2) len=0 -> 2

This was invisible because nothing failed. A Simple caller checks
`span.len() != n`, reads the mismatch as "extern not backed", and falls back to
scalar — the documented, correct fallback doing exactly its job over a bug.

**Defect 3 — the glyph mask blend read packed bytes as tagged slots.** With the
length fixed, the content check turned up **819 mismatches out of 1640** in the
mask kernel while the DB and coverage kernels were exact. A `[u8]` is
`RT_CORE_ARRAY_FLAG_BYTES` (packed) in the native runtime and one tagged int64
slot per element in the boxed one; the C twin assumed slots unconditionally and
blended every glyph pixel against garbage. The flag was private to
`runtime_native.c`, so the kernel could not ask — hence a public
`rt_array_is_byte_packed`, and the kernel now resolves the representation from
the array instead of assuming it.

After all three: **2460 values checked in a native binary, 0 mismatches, 7 zmm
present.**

### The gate

`scripts/check/check-native-simd-kernels-real.shs`, driving
`test/01_unit/check/native_simd_kernel_probe.spl`. It builds a real native
binary, runs it, and checks CONTENT against oracles for the DB bitmap AND, the
glyph mask blend and the soft-shadow coverage blend — then disassembles the
binary and fails if it contains no zmm.

Content, not length, is the point: an in-place kernel's failure path returns
its input, so a length check cannot distinguish success from failure. That trap
is why the percent blend looked healthy — `len=4` was returned by both the
working and the failing path, and it took comparing `0xFF7F7F7F` against the
input to tell them apart.

Advisory in CI (`continue-on-error`): it needs a built seed and llvm-objdump
and exits 2 without them, which as a blocking gate would fail every runner that
has neither.

### What is now true

A shipped native binary carries real AVX-512 and its SIMD kernels return
correct values. The DB bitmap path is AVX-512 accelerated end to end — kernel
present, reached by the caller, and bit-exact over 40 lengths. The glyph and
soft-shadow paths are correct and reached; their kernels remain
auto-vectorized rather than explicit-lane, so on a gcc link they are AVX2. The
explicit-lane treatment given to the DB AND is owed to them next, and the gate
above will show it the moment it lands.
