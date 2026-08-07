# T16 — blend-span kernels are unreachable as a native ABI symbol: three divergent implementations, only two complete

**Filed:** 2026-08-07 · **Severity:** high (perf-plan unit blocked; native ABI gap)
**Source unit:** `doc/03_plan/ui/perf/render_perf_replan_parallel_teams_2026-08-07.md` T16
("Verify the blend-span C symbols are linked and bit-exact")
**Binary under test:** `bin/release/x86_64-unknown-linux-gnu/simple`, md5
`70476ca038e184fecba4f910b0db9b18`, 58,954,304 bytes, mtime 2026-08-07 22:39:42.
**Provenance: still the Rust seed** — `bin/simple --version` prints:
```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
Simple Language v1.0.0-beta
```
This refutes the task premise that the 2026-08-07 22:39 redeploy was a
self-hosted pure-Simple redeploy that unblocked T16. `.claude/rules/bootstrap.md`
"KNOWN BLOCKER" section (Stage 3 `ByteOrder`/`Effect` self-host failure) is
still open and matches: no full-bootstrap self-host redeploy has landed since
that doc was written. The 22:39 artifact is a fresh **seed** build, which
`.claude/rules/bootstrap.md:24-36` explicitly warns is the exact ad hoc
`cargo build --release` + copy pattern that "resets the clock on the next
lane's binary-provenance check without fixing anything."

## 1. Acceptance criterion #1 — does the symbol resolve at link time? NO.

```
$ nm bin/release/x86_64-unknown-linux-gnu/simple | awk '$3 ~ /^rt_engine2d_simd/ {print}'
000000000226c360 T rt_engine2d_simd_blend_row_u32
000000000226c720 T rt_engine2d_simd_copy_row_u32
000000000226cab0 T rt_engine2d_simd_copy_span_u32
000000000226d270 T rt_engine2d_simd_fill_rows_u32
000000000226cfd0 T rt_engine2d_simd_fill_row_u32
000000000226d2a0 T rt_engine2d_simd_fill_span_u32
```
`rt_engine2d_simd_blend_span_u32` and `rt_engine2d_simd_blend_const_span_u32`
are **absent** — not `T`, not `U`, not present at all, in the deployed binary.

Same result one layer down, in the static archive the binary links
(`src/compiler_rust/target/release/libsimple_runtime.a`, mtime
2026-08-07 18:43:46, i.e. built *after* `runtime_simd_dispatch.c`'s
2026-08-07 01:29:42 mtime — so this is not a stale-object-cache problem):
```
$ nm src/compiler_rust/target/release/libsimple_runtime.a | grep -i engine2d_simd
                 U rt_engine2d_simd_blend_row_u32
                 U rt_engine2d_simd_copy_row_u32
                 U rt_engine2d_simd_copy_span_u32
                 U rt_engine2d_simd_fill_rows_u32
                 U rt_engine2d_simd_fill_row_u32
                 U rt_engine2d_simd_fill_span_u32
0000000000000000 T rt_engine2d_simd_blend_row_u32
0000000000000000 T rt_engine2d_simd_copy_row_u32
0000000000000000 T rt_engine2d_simd_fill_rows_u32
0000000000000000 T rt_engine2d_simd_fill_row_u32
0000000000000000 T rt_engine2d_simd_fill_span_u32
0000000000000000 T rt_engine2d_simd_copy_span_u32
```
Again, blend_span/blend_const_span present nowhere, siblings all present.

## 2. Root cause — NOT a build-packaging/staleness issue. There are three independent implementations of this kernel family, and the one that actually gets linked into the native ABI is missing the two new kernels.

`nm -A` (archive-member-qualified) on the six working siblings shows they are
**not** provided by the C translation unit at all in this link:
```
$ nm -A src/compiler_rust/target/release/libsimple_runtime.a | grep -w rt_engine2d_simd_fill_span_u32
libsimple_runtime.a:simple_runtime.simple_runtime.fabff61dd2ea1958-cgu.09.rcgu.o:                 U rt_engine2d_simd_fill_span_u32
libsimple_runtime.a:simple_runtime.simple_runtime.fabff61dd2ea1958-cgu.14.rcgu.o:0000000000000000 T rt_engine2d_simd_fill_span_u32
```
Both are Rust codegen-unit objects (`.rcgu.o`), not C objects. Confirmed by
source: `src/compiler_rust/runtime/src/value/engine2d_simd_ops.rs` defines
`pub extern "C" fn rt_engine2d_simd_fill_row_u32/fill_rows_u32/copy_row_u32/
fill_span_u32/copy_span_u32/blend_row_u32` (lines 82-180+) — a **second,
independent Rust reimplementation** of the same kernels, exported under the
identical C-ABI names. This is the definition that actually satisfies the
linker for the deployed native ABI; a standalone compile of the C file proves
the C definitions are also syntactically fine and would export the same names
(`gcc -c -O2 -std=gnu11 src/runtime/runtime_simd_dispatch.c` → `nm` shows both
`rt_engine2d_simd_blend_span_u32` and `_const_span_u32` as `T`), but the C
archive member (`runtime_sffi_c`, built by
`src/compiler_rust/runtime/build.rs::compile_c_runtime_sources`) is linked
with plain `-lstatic=runtime_sffi_c` (selective extraction, not
`+whole-archive` — see build.rs's own comment on that branch), and nothing in
the Rust crate graph references the C names, so the C member is never pulled
in. **`src/runtime/runtime_simd_dispatch.c`'s kernel bodies (including the
two new blend-span ones) are dead code for this link configuration.**

`engine2d_simd_ops.rs` (`simple_runtime` crate — the native-ABI provider) has
**no** `rt_engine2d_simd_blend_span_u32` or `_blend_const_span_u32` function
at all:
```
$ grep -n 'pub extern "C" fn rt_engine2d_simd' src/compiler_rust/runtime/src/value/engine2d_simd_ops.rs
82:pub extern "C" fn rt_engine2d_simd_fill_row_u32(...)
88:pub extern "C" fn rt_engine2d_simd_fill_rows_u32(...)
102:pub extern "C" fn rt_engine2d_simd_copy_row_u32(...)
112:pub extern "C" fn rt_engine2d_simd_fill_span_u32(...)
130:pub extern "C" fn rt_engine2d_simd_copy_span_u32(...)
174:pub extern "C" fn rt_engine2d_simd_blend_row_u32(...)
```
That is the actual gap: **T16's design plan
(`engine2d_simd_blend_span_kernel_design_plan_2026-08-07.md` §4) only specified
wiring the C kernel + the interpreter bridge
(`interpreter_extern/simd.rs`/`mod.rs`, both of which ARE wired and present
in the deployed binary as mangled `interpreter_extern::simd::...` symbols) —
it never specified adding the two new functions to `engine2d_simd_ops.rs`,
the crate that provides the actual native-callable C-ABI symbol.** A third,
independent implementation would be needed there, following the exact pattern
already used for `blend_row_u32` (lines 156-180: `blend_pixel` + iterator
zip), to make `rt_engine2d_simd_blend_span_u32`/`_const_span_u32` resolve as
linked native symbols the way their five siblings do.

## 3. What IS proven (acceptance criterion #2, partial)

Per the interpreter bridge in `interpreter_extern/simd.rs:1557-1601` (present
in the deployed binary, confirmed via `nm` showing the mangled
`_ZN...interpreter_extern4simd31rt_engine2d_simd_blend_span_u32...` and
`...37rt_engine2d_simd_blend_const_span_u32...` symbols), and the spec at
`test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_isa_provider_spec.spl:327-393`,
this session's predecessor already established the Rust interpreter bridge is
bit-exact against the scalar oracle for `sa==0`, `sa==255`, 64/4096-length,
and zero-length spans — but that spec's own honesty note (lines 306-325)
already documents that this proves only the interpreter bridge, not the
native/C path, because `bin/simple test`/`simple run` route ALL extern calls
through the Rust bridge in both interpreter and JIT modes regardless of
whether a native symbol exists. That finding stands unchanged; this bug adds
the missing half: the native-ABI ("truly compiled/linked") symbol does not
exist anywhere reachable, not merely "unverified this session."

## Acceptance verdict

T16's stated acceptance ("the symbol resolves at link time — prove it, `nm`,
not inference; every kernel is bit-exact vs scalar; a non-bit-exact kernel is
not registered") is **NOT MET** for `rt_engine2d_simd_blend_span_u32` /
`rt_engine2d_simd_blend_const_span_u32` as native-ABI symbols. It IS met for
the Rust interpreter-bridge path (previously established, re-confirmed by
symbol presence in this binary).

## Fix required (not done here — scope mismatch with an isolated-bootstrap unit)

Add `rt_engine2d_simd_blend_span_u32`/`_blend_const_span_u32` to
`src/compiler_rust/runtime/src/value/engine2d_simd_ops.rs`, mirroring
`rt_engine2d_simd_blend_row_u32`'s existing `blend_pixel` per-element loop
(span-bounded like `fill_span_u32`/`copy_span_u32` in the same file, not
`blend_row_u32`'s whole-array shape). This is a **pure Rust crate change**
(`src/compiler_rust/runtime`), not a self-host/Stage-3 concern — it does not
require the blocked full-bootstrap window, only a normal seed rebuild + `nm`
re-verification. Once added, re-run this bug's `nm` commands against a fresh
build to close it out, then re-run the existing spec's blend_span/
blend_const_span `describe` blocks and update their titles to drop the
"C kernel unverified" caveat.

The `src/runtime/runtime_simd_dispatch.c` bodies remain dead code for the
current link configuration; leaving them in place is harmless (matches the
proven-correct scalar/oracle math) but does not, by itself, close this gap —
whole-archive linking or an explicit reference would be a separate, larger
change (`CARGO_FEATURE_RUNTIME_SYMBOL_TABLE`) not scoped to T16.

## Files
- `src/runtime/runtime_simd_dispatch.c:1628,1649` — C kernels (dead code, this link config)
- `src/compiler_rust/runtime/src/value/engine2d_simd_ops.rs:82-180` — native-ABI provider (missing blend_span/blend_const_span)
- `src/compiler_rust/compiler/src/interpreter_extern/simd.rs:1554-1601`, `mod.rs:1709-1710` — interpreter bridge (complete, proven bit-exact)
- `src/compiler_rust/runtime/build.rs:117-215` (`compile_c_runtime_sources`), `:295-330` (`collect_c_runtime_exports`, filters `runtime_simd_dispatch.c` to `rt_opencl_*` only for the symbol-table generator)
- `test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_isa_provider_spec.spl:306-393`
- `doc/03_plan/ui/perf/engine2d_simd_blend_span_kernel_design_plan_2026-08-07.md` §4 (design gap: never specified `engine2d_simd_ops.rs`)
- `doc/03_plan/ui/perf/render_perf_replan_parallel_teams_2026-08-07.md` T16 (this unit)
