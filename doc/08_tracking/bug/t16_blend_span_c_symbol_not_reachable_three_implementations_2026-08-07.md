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

## RESOLVED (native-ABI symbol; 2026-08-07, follow-up session)

Added `rt_engine2d_simd_blend_span_u32` and `rt_engine2d_simd_blend_const_span_u32`
to `src/compiler_rust/runtime/src/value/engine2d_simd_ops.rs`, mirroring
`blend_row_u32`'s `blend_pixel` per-element loop, span-bounded like
`fill_span_u32`/`copy_span_u32`. Semantics were pinned to the
**already-proven-bit-exact interpreter bridge**
(`interpreter_extern/simd.rs:1557-1614`), not the C file or the sibling
`fill_span_u32`/`copy_span_u32` `.max(0)` clamp convention — the bridge
**rejects** a negative `dst_offset`/`src_offset`/`offset` (returns the
destination array unchanged) rather than clamping it to 0. An initial draft
used `.max(0)` by analogy to `fill_span_u32` and was corrected before landing;
a dedicated unit test (`hosted_blend_span_rejects_negative_offsets_instead_of_clamping`)
pins the reject behaviour so a future edit can't silently regress it back to
clamp semantics.

**Verified (incremental release build from a warm `target/` — no `cargo
clean`, no full bootstrap):**
```
$ nm src/compiler_rust/target/release/simple | grep "T rt_engine2d_simd_blend"
... T rt_engine2d_simd_blend_const_span_u32
... T rt_engine2d_simd_blend_row_u32
... T rt_engine2d_simd_blend_span_u32

$ nm -A src/compiler_rust/target/release/libsimple_runtime.a \
    | grep -E 'rt_engine2d_simd_blend_(span|const_span)_u32' | grep -v ' U '
libsimple_runtime.a:simple_runtime.simple_runtime.<hash>-cgu.14.rcgu.o:0000000000000000 T rt_engine2d_simd_blend_const_span_u32
libsimple_runtime.a:simple_runtime.simple_runtime.<hash>-cgu.14.rcgu.o:0000000000000000 T rt_engine2d_simd_blend_span_u32
```
Both resolve as `T`, exactly one definition each, from a Rust `.rcgu.o`
codegen unit (not the still-dead C translation unit) — the archive-member
qualification the original report used to diagnose the gap now shows it
closed the same way.

`cargo test --release -p simple-runtime engine2d_simd_ops`: **10/10 passed**
(the 6 pre-existing + 2 new hosted-ABI tests + the new negative-offset-reject
test + the existing hosted-span-clamp test). A full `cargo test --release -p
simple-runtime` run shows 8 pre-existing failures unrelated to this module
(`executor::tests::test_isolated_thread_spawn_with_args_and_join*`,
`loader::package::format::tests::test_manifest_section_rejects_partial_runtime_variants_trailer`,
`loader::settlement::native::tests::test_native_lib_manager`,
`value::collections::tests::test_dict_invalid_value`,
`value::collections::tests::test_low_heap_tagged_values_do_not_crash_collection_runtime`,
`value::collections::tests::test_string_char_at_out_of_bounds`,
`value::heap::attr_tests::owner_attribution_orders_by_live_bytes_and_frees_settle`)
— none touch `engine2d_simd_ops` or any module this change modified; this
session's diff is 92 purely-additive lines in exactly one file, confirmed via
`git status --porcelain -- src/compiler_rust/runtime` before building.

**Spec run — honest scope, not upgraded to "native-path proven":** re-running
`simd_isa_provider_spec.spl`'s `blend_span`/`blend_const_span` `describe`
blocks does **not** newly verify the native path and their titles still say
"C kernel unverified" **intentionally** — `bin/simple test`/`simple test`
routes every extern call through the Rust **interpreter bridge**
(`interpreter_extern/simd.rs`) in both interpreter and JIT modes regardless of
whether a native symbol exists, exactly as this bug doc's §3 already
documented. Worse, the test runner's child-binary resolution
(`test_runner_single.spl::find_simple_binary`) defaults to `/proc/self/exe`
of the *invoking* binary, which in this shared tree is the stale deployed
`bin/release/x86_64-unknown-linux-gnu/simple` seed unless
`SIMPLE_BINARY=<fresh-binary-path>` is set explicitly — a first spec attempt
without it printed `child binary: .../bin/release/x86_64-unknown-linux-gnu/simple`
(then hit `Process timed out` during the outer harness's own module-load
phase) and thus would have proven nothing about this change either way. A
second attempt with `SIMPLE_BINARY` pinned confirmed
`child binary: /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple`
and, after a ~353s module-load/compile phase (interpreted-mode module lint
tax, not a hang), produced a real verdict:
```
=========================================
Test Summary
=========================================
Files: 1
Passed: 24
Failed: 0
Results: 24 total, 24 passed, 0 failed
Duration: 352566ms

PASS test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_isa_provider_spec.spl
```
All 24 examples pass, including every `blend_span`/`blend_const_span` `it` —
this is a regression check confirming the freshly-built binary's interpreter
bridge (unmodified by this session) still agrees with the oracle, run against
the same binary that now also carries the new native-ABI symbols. It is not,
and is not being represented as, new evidence for the native/C path — that
evidence remains `nm` (above) and the cargo unit tests (above), per the
decision rule already stated in this doc's §3.

**Native ABI symbol gap: CLOSED.** Interpreter-bridge path: unchanged, still
proven bit-exact (pre-existing). Self-hosted pure-Simple **LLVM backend**
registration gap: **left OPEN, not touched** — see residual below.

## Residual RESOLVED (2026-08-07, follow-up session): self-hosted MIR/LLVM registration landed

The two mechanical, pattern-matched additions this section calls for below
are now landed, mirroring `a399483d`'s registration of `fill_span_u32`/
`copy_span_u32`:

- `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`
  (`bootstrap_resolved_call_return_type`, ~line 1203): added
  `rt_engine2d_simd_blend_span_u32` and `rt_engine2d_simd_blend_const_span_u32`
  to the `Array(U32)` return-type OR-chain, alongside `rt_engine2d_simd_fill_span_u32`
  / `rt_engine2d_simd_copy_span_u32`.
- `src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl`
  (~line 178-179, immediately after the `copy_span_u32` declare): added
  `declare ptr @rt_engine2d_simd_blend_span_u32(ptr, i64, ptr, i64, i64)` and
  `declare ptr @rt_engine2d_simd_blend_const_span_u32(ptr, i64, i64, i64)`,
  matching the Rust signatures `(dst, dst_offset, src, src_offset, count)` and
  `(dst, offset, count, const_color)` in `engine2d_simd_ops.rs`.

This landed via the interpreter path only (this session had no working
self-hosted/Stage-3 build either, same blocker as noted below) — verified by
`test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl` staying **45/45
passed, 0 failed** after the change (regression check; this spec does not
exercise the native LLVM backend directly). The **unblock condition below
still applies** for verifying the LLVM-backend declare lines against a real
self-hosted build once Stage 3 is fixed — that verification gap is not closed
by this session, only the source registration itself.

## Residual: self-hosted LLVM backend registration (not fixed here, blocked on Stage 3)

`blend_row_u32`'s C-ABI signature is registered in the self-hosted pure-Simple
LLVM codegen backend at two sites; `fill_span_u32`/`copy_span_u32` are also
registered there (their span-family precedent, not `blend_row_u32`'s). The two
new span functions are **not** registered at either site:

- `src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl:181`
  — needs `declare ptr @rt_engine2d_simd_blend_span_u32(ptr, i64, ptr, i64, i64)`
  and `declare ptr @rt_engine2d_simd_blend_const_span_u32(ptr, i64, i64, i64)`
  immediately after the existing `copy_span_u32` declare line, matching its
  C-ABI shape.
- `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1203` — both
  names need adding to the `Array(U32)` return-type OR-chain (the same list
  `rt_engine2d_simd_fill_span_u32`/`rt_engine2d_simd_copy_span_u32` are already
  in). Without this, a call falls through to the generic i64 default — the
  exact failure class already documented at
  `asm_constraints_helpers.spl:161-173` for `rt_array_repeat` (bug #149:
  "defined with type 'i64' but expected 'ptr'").
- Precedent note: the span family (`fill_span`/`copy_span`) takes `declare` +
  return-type-registry entries but **not** a `defined_func_names` entry — that
  third registration is row-family-only (`fill_row`/`fill_rows`/`copy_row`/
  `blend_row`). The two new functions should follow the span-family pattern,
  not the row-family one.

**Why not fixed in the same session:** `.claude/rules/bootstrap.md`'s KNOWN
BLOCKER — Stage 3 self-host (`unresolved type: ByteOrder` in
`cache_validator.spl`, then an `Effect` facade collision) — means there is
currently no way to build and verify a change to `src/compiler`'s own LLVM
backend; landing an edit there unverified violates this session's own
"if the build or verification fails, land nothing" instruction, and this file
is part of the compiler that any bootstrap would need to recompile itself
with. **Unblock condition:** fix the Stage 3 defect (tracked separately at
`doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`),
then land the two mechanical, pattern-matched additions above and verify with
a real self-hosted build + a native-LLVM-backend call site exercising
`rt_engine2d_simd_blend_span_u32`/`_blend_const_span_u32`.

## Fragility note: the span-bridge spec couples to implementation source text

`test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl`'s "cross-mode
return-array span bridge" example does not only assert on span-bridge
*behavior* — it also constrains exact identifiers inside
`backend_software.spl`'s implementation. That coupling is what forced the
unrelated `safe_count` → `count` rename of `sw_fill_raw_span`'s clipped local
in `a399483d` (same commit that wired the span-bridge intrinsics into MIR
lowering and LLVM decls) — a pure rename, not a behavior change, done solely
to satisfy the spec's source-text expectation. A spec that fails on a
same-behavior rename is testing implementation shape, not the contract it
claims to cover, and will keep forcing incidental renames (or blocking
legitimate ones) as this code evolves. Recommend migrating this example to
behavioral assertions (actual span-fill/copy/blend output on representative
inputs) rather than exact source-text matching, the next time this spec is
touched.
