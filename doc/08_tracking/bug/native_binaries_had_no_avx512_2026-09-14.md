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

## Web rendering: explicit lanes for the glyph and shadow kernels

The section above closed by saying the glyph and soft-shadow kernels were
correct and reached but still auto-vectorized, so AVX2 on a gcc link. Both now
have explicit lanes.

Native binary zmm count, measured at each step: **0 -> 7 (DB) -> 45 (glyph)
-> 88 (shadow)**, with `2460 values checked, 0 mismatches` holding throughout.

**The `/255` had to stay exact.** `(x * 32897) >> 23` equals `x / 255` for every
x in 0..65025, proven exhaustively over that range rather than argued — and
65025 is the whole range `fg*a + d*(255-a)` can produce with fg, d <= 255. The
shadow kernel needs both divisors and they are NOT interchangeable: `cov*alpha`
divides by 255 while the blend divides by 256, so the blend keeps a shift and
only the alpha term uses the constant. Borrowing one for the other shifts every
shadow pixel.

**`a == 0` (glyph) and `cov <= 0` (shadow) select the ORIGINAL slot back**
rather than blending. Blending would give the right colour but force alpha to
0xFF, while the scalar path returns the destination untouched — a difference
that only appears on a non-opaque destination, which a parity test over opaque
ramps would never catch.

**AVX512DQ, not just F+BW.** `_mm512_mullo_epi64` is a DQ instruction; GCC
caught it as `inlining failed ... target specific option mismatch` where clang
accepted the F+BW attribute silently. The CPUID probe checks DQ too, so the
lane path cannot run on a part that lacks it.

### Known limit, stated rather than papered over

The shadow kernel's `/256` on `cov*cov_y` is an arithmetic shift, which is
floor, while C integer division truncates toward zero. They agree for
non-negative values, and coverage is 0..256 by construction (`_phi256`), but a
negative `colcov` would diverge. The probe exercises 0..256 only, so this is
reasoned rather than tested.

`glyph parity 6/6`, `soft-shadow parity 9/9`, `rounded interior 7/7`,
`check-simd-kernels-vectorized 11/11`,
`check-native-simd-kernels-real PASS — 2460 values, 88 zmm`.

## The two numbers that were missing

**Soft-shadow kernel: 5.8x.** Measured in NATIVE binaries, because the native
clocks are unusable (below) and the interpreter could not run the scalar
baseline in tolerable time. Two binaries identical but for the path under test,
plus a no-op binary to subtract startup; min of 5 runs each:

    40000 rows x 600 px = 24M shadow pixels
    startup (no-op)  92 ms
    scalar          1345 ms  ->  1253 ms of work
    kernel           308 ms  ->   216 ms of work

An earlier attempt at 4000 rows was DISCARDED rather than reported: startup
varied 80-185 ms, which was larger than the signal. Scaling the work 10x put it
an order of magnitude above the noise. Parity was proven separately
(`pixel_diffs=0`) before any timing was believed — a fast wrong answer is not a
speedup.

**A third native defect: the clocks return -1.** `rt_time_now_micros`,
`rt_time_now_nanos` and `rt_time_ms` all answer -1 in a native binary while the
program around them runs correctly. Any in-binary benchmark silently reports
zero elapsed time. Not fixed here; it is why the measurement above is external.

## GPU and CPU in one test

`test/01_unit/check/gpu_cpu_simd_combined_spec.spl`, 3/3. It dispatches a real
Vulkan compute clear, reads the pixels back, computes the same fill through the
CPU SIMD span kernel, and compares them — **4096 pixels, bit-for-bit**. Then it
exercises the AVX-512 CPU kernels against their oracles in the same process, so
a regression in either lane fails one test.

Comparing PIXELS rather than frame times is the point. A stubbed GPU path still
returns plausible timings: earlier in this work `default = []` left the vulkan
feature off, and every GPU benchmark was a no-op that still produced numbers.
Absence of a device is reported as a skip with a reason, never as agreement.

Writing it found a real bug in my own dispatch: `clear` is a 1D dispatch with
`local_size_x=256`, and a 2D 8x8 dispatch covered exactly half the buffer —
2048 of 4096 pixels differing, which is what a half-covered buffer looks like.

## "Reasoned, not tested" was wrong — testing it found a real bug

The previous section left the shadow kernel's `/256` as an arithmetic shift
(floor) where C division truncates, argued safe because both results are <= 0
for negative coverage and both paths then skip. Testing the negative domain
gave **84 mismatches**, so the argument was wrong — and for a reason neither
half of it mentioned.

`engine2d_unbox_pixel` truncates **unsigned**: `(uint32_t)((uint64_t)v >> 3)`.
A `[i32]` coverage of `-1` therefore arrives in the C kernel as `4294967295`
and blends at full strength, while the Simple twin reads `(colcov[i]).to_i64()`
as `-1` and skips the pixel. A genuine divergence between the two
implementations, in the representation rather than in the arithmetic.

Fixed by sign-extending the low 32 bits in all three paths — the AVX-512 lanes
(`slli 32` then `srai 32`), the lane kernel's scalar tail, and the plain C
fallback — so both sides see the same number. With that, floor and truncate
genuinely do agree, because every negative value now reaches the `<= 0` skip on
both sides.

`2760 values checked in a native binary, 0 mismatches, 90 zmm`, negative
coverage included.

The lesson is the one this record keeps repeating: an argument about output is
a testable claim, and the cheap test is worth more than the careful reasoning.

## The native clocks are fixed

`rt_time_now_ns` and `rt_time_now_unix_micros` both called `clock_gettime`,
which MinGW maps onto `clock_gettime64` — a symbol this runtime does not link.
The native linker reported it unresolved and substituted a generated stub, so
every call failed and every clock returned -1. Any in-binary benchmark silently
measured zero elapsed time.

Windows branches added: `QueryPerformanceCounter` for the monotonic clock
(seconds and sub-second remainder scaled separately so the nanosecond
conversion cannot overflow) and `GetSystemTimeAsFileTime` for the wall clock,
rebased from the 1601 epoch. Verified: the monotonic clock advances 71 ms
across a busy loop that takes 71 ms, and the wall clock agrees with the host's
`date +%s` to within the sub-second digits it does not print.

### The shadow number, re-measured with the fixed clock

    20000 rows x 600 px = 12M shadow pixels, in-binary timing
    scalar  660006 / 590886 / 595254 us
    kernel   94925 /  95560 / 105220 us
    pixel_diffs = 0 on every run

**6.2x**, which independently corroborates the 5.8x obtained earlier by
external process timing with startup subtracted. Two unrelated methods, the
same answer.

## The DB LIBRARY path, not just the extern

The gate previously called `rt_db_bitmap_and_u32` directly. That proves the
kernel is in the binary; it does not prove the code a server runs reaches it.
`accel.spl` wraps every call in a length check and silently falls back to its
scalar twin when the extern looks unbacked — which is precisely how a dead
kernel stayed invisible through three gates.

The probe now calls `row_bitmap_and_words`, `row_bitmap_or_words` and
`row_bitmap_andnot_words` — the library's public API, what a query engine calls
— and compares each against its `_scalar_` twin. Natively:
**6288 values checked, 0 mismatches, 90 zmm present.**

That is the DB path accelerated end to end: library API -> extern -> CPUID
dispatch -> AVX-512 lanes, with results identical to the scalar reference at
every length 1..48.

## Why there is still no fully-linked server executable

Filed rather than fixed, with the diagnosis, because it is a native-lane
infrastructure problem and not a SIMD one.

Two independent blockers:

1. **A codegen bug.** `src/lib/gc_async_mut/web/browser_session_runtime.spl`
   fails to compile natively — `codegen: 1 function body/bodies failed to
   compile: [BrowserDomEventExecutor.listener_indices_for_target_event]`. That
   stops `src/app/browser/main.spl` outright.

2. **An incomplete C source set.** The renderer module links against `rt_mmap`,
   which IS implemented — in `platform/platform_win.h`, included only by
   `runtime.c`, which is NOT in the native build's `runtime_inputs` list
   (`pipeline/native_project/tools.rs`). That list's own comments record why:
   adding `runtime.c` wholesale "collides on 53/69 symbols, same class as the
   disproved runtime_native.c fix". The sanctioned pattern is a small
   self-contained TU defining exactly the missing symbols, as
   `runtime_core_io_exports.c` did for twelve of them.

Note what this is NOT: the 23 symbols the linker first reported are mostly
present in `runtime.c` already (`rt_get_args`, `rt_black_box`,
`rt_time_now_seconds`, `rt_file_fsync`, `rt_atexit_install`,
`rt_signal_install`). Only `rt_mmap` needed hunting, and it was found. This is a
link-set curation problem with documented prior failures, not missing code.

Neither blocker affects the AVX-512 result: whether the browser app links is
orthogonal to whether the kernels a server calls are AVX-512, and the library
check above answers that directly.

## The web-server parse path: linked with AVX-512, but the binary SEGVs

An HTTP server's SIMD hot path is CRLF scanning, and that chain IS wired:
`http_core.spl:234` calls `simd_find_byte` -> `rt_simd_find_byte_span` ->
AVX-512. Confirmed by building `chunked_body_end_scan` /
`decode_chunked_bounded` into a native binary:

  * builds clean (7 modules), no unresolved symbols, no stub flags needed;
  * **90 zmm** present;
  * `rt_simd_find_byte_span` linked.

Then it **segfaults on run** (rc 139). Nothing SIMD-specific: the same native
lane that cannot link the browser app cannot run this either, and it is the
same class as the documented stage-binary SEGVs
(`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`).

So for the web server the evidence stops one step short of the DB result: the
AVX-512 scanner is demonstrably compiled into the binary and reachable from the
HTTP parser, but the binary does not execute, so no parity run backs it. The DB
library path has both (runs, 6288 values, 0 mismatches); this one has linkage
and instructions only. Stated that way rather than rounded up.

Filed as native-lane work, not SIMD work. The three blockers now on record for
that lane are: a codegen failure
(`BrowserDomEventExecutor.listener_indices_for_target_event`), an incomplete C
source set (`rt_mmap` reachable only through `runtime.c`), and this runtime
SEGV.

## The web server could not find a single CRLF natively

Chasing the SEGV above turned up something worse than the SEGV. Bisecting the
crashing probe showed `chunked_body_end_scan` itself runs fine — so the scanner
was reachable, and could be compared directly against its scalar twin:

    NATIVE (before)                    INTERPRETER
    from=0  simd=-1  scalar=5          from=0  simd=5   scalar=5
    from=6  simd=-1  scalar=20         from=6  simd=20  scalar=20
    from=24 simd=-1  scalar=38         from=24 simd=38  scalar=38

`simd_find_byte` returned **-1 for every input** in a native binary. Over a
sweep: 2930 mismatches out of 2986.

Same root cause as the glyph mask blend, in a kernel I had not looked at:
`rt_simd_find_byte_span` read a `[u8]` as tagged int64 slots. The comment above
the loop asserted that representation outright — "SplArray stores one int64_t
slot per element (tagged), NOT packed bytes" — which is true of the boxed
runtime and false natively, where `[u8]` is `RT_CORE_ARRAY_FLAG_BYTES`.

This is not a slow path or a missed optimization. `_crlf_from`
(`http_core.spl:234`) is how an HTTP server finds header boundaries, so a
natively built web server could not locate a single CRLF — while the
interpreter's Rust twin was correct and every existing gate stayed green.

`rt_simd_bytes_equal_span` had it too, and each side of that comparison is now
resolved independently: nothing requires both arguments to share a
representation.

After: **2986 scan comparisons, 0 mismatches**, and the gate covers it —
`PASS — 9274 value(s) checked in a native binary, 90 zmm present`.

That makes three kernels found with the same defect (glyph mask, byte find,
bytes equal) and one representational sibling (signed coverage). The pattern is
worth naming: every one of them assumed a single element representation,
compiled cleanly under both, and was verified only through the interpreter —
which uses the other implementation entirely.
