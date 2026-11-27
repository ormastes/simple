# Codegen Cranelift ISA/config SFFI wrappers share the io_file_open text-ABI mis-expansion defect — 2026-10-22

## Symptom

`src/lib/nogc_sync_mut/sffi/codegen.spl` hand-expands text arguments to
`(ptr, len)` with `rt_string_data`/`rt_string_len` for the Cranelift module
and ISA-family externs:

- `cranelift_new_aot_module(name, target)` → `rt_cranelift_new_aot_module_triple(rt_string_data(name), rt_string_len(name), rt_string_data(target), rt_string_len(target))`
- `cranelift_new_aot_module_config_v2(name, target, cpu, opt_level, features)` → 9-arg `spl_cranelift_new_aot_module_config_v2(...)`
- `cranelift_aot_isa_feature_v2(module, feature)` → `spl_cranelift_aot_isa_feature_v2(module, rt_string_data(feature), rt_string_len(feature))`

This is the SAME pattern that made `io_file_open` return -1 for every entry
read in seed-built native binaries (fixed 2026-10-22 in
`src/lib/nogc_sync_mut/sffi/fs.spl` by declaring the extern in text form and
letting the compiler's text-ABI registry perform the expansion; the rebuilt
seed's call-site lowering re-expanded the already-extracted raw pointer,
verified by candidate disassembly). These externs carry the same expanded
`[I64, I64, ...]` specs in
`src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:1825-1827` and have
no `text_arg_indices` rows in `codegen/instr/calls.rs`, so the manual
expansion is the only text handling — and it is exactly the shape the seed
mis-lowers.

Observable effect: in a seed-built (AOT) compiler binary, the ISA-feature
readback `cranelift_aot_isa_feature_v2` receives `rt_string_data(address)`
instead of `rt_string_data(feature_text)`, so the Cranelift runtime looks up
a garbage feature name and returns a garbage/0 i64; the configured-module
constructors similarly build modules under garbage names/targets. Under the
Rust seed's own execution the same source behaves correctly, so the defect
only surfaces in self-hosted binaries — precisely the configuration the
stage-2/3/4 bootstrap lanes build.

## Status

Open. Source-level fix prepared in the same shape as the accepted
`rt_io_file_open` fix: declare these externs with `text` parameters
(e.g. `extern fn spl_cranelift_aot_isa_feature_v2(module: i64, feature: text) -> i64`)
and pass the text values directly. Runtime-side (Rust) behavior is
correct; no runtime change needed. Not yet applied because the bootstrap
lane owned the tree at filing time.

## Evidence

- `runtime_sffi.rs:1822-1827` — expanded I64 specs for the whole
  `rt_cranelift_*` / `spl_cranelift_*` family.
- `codegen.spl:38-49` — the manual `rt_string_data`/`rt_string_len`
  expansion at the call sites.
- Sibling bug: `stage2_sanity_p2_add_zero_source_files_scv_cold_snapshot_2026_10_22.md`
  (io_file_open chain, fixed).

**Revalidated 2026-11-02: still plausible because the report title (Cranelift ISA/config SFFI wrappers hand-expand text with rt_string_data/rt_stri) has no merged fix or passing regression cited in its tracking doc; no merged fix commit with a passing regression is cited in this doc.**

## Policy re-check and re-scope (2026-11-02, lane a6dffc9c/p12-8)

Checked against current policy/design: **still valid, re-scoped to: all
hand-expanded `rt_cranelift_*` text wrappers in `sffi/codegen.spl`; fix via the
two-arg twin route (`fs.spl` precedent) or seed+Simple text-registry rows
(`calls.rs` `text_arg_indices`, `text_extern_abi.spl` + arity + parity spec,
`interpreter_extern/cranelift.rs` accepting text); needs seed-built native
red/green.** Difficulty raised 3 -> 4. No code change made.

The earlier "Status" claim that only the `text` declaration is needed is wrong:
declaring the externs as `text` is a no-op until the registries carry rows.

File:line list:

- `src/lib/nogc_sync_mut/sffi/codegen.spl` ~34-53: hand expansion for
  `cranelift_new_module`, `cranelift_new_aot_module`,
  `cranelift_new_aot_module_config_v2`, `cranelift_aot_isa_feature_v2`; the same
  pattern recurs in `cranelift_declare_string_data`,
  `cranelift_declare_global_data*`, `cranelift_function_addr_in_func`,
  `cranelift_begin_function` and later wrappers (wider than the three named).
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs:3132` `text_arg_indices`
  (no rows for these symbols; `rt_io_file_open` precedent at ~3301).
- `src/compiler/50.mir/text_extern_abi.spl:40` `text_arg_indices`, `:239`
  `text_extern_semantic_arity`; parity spec
  `test/01_unit/compiler/mir/text_extern_abi_seed_parity_spec.spl`.
- `src/compiler_rust/compiler/src/interpreter_extern/cranelift.rs:199`
  (`spl_cranelift_aot_isa_feature_v2`) and the module constructors read raw
  `i64` ptr/len via `expect_i64`; they break if the wrapper passes text.
- `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:1866-1872` expanded I64 specs.
- `src/lib/nogc_sync_mut/sffi/fs.spl:332` records that multi-arg text externs
  mis-pass the length in seed-produced candidates (why `fs.spl` moved to
  two-arg twins); `spl_cranelift_new_aot_module_config_v2` mixes text and
  scalar args and is the highest-risk form.

## Investigation 2026-11-03 (lane work/cranelift-text-abi) - premise NOT confirmed, status stays open

Static finding (origin/release/1.0.0 `27e65c24371`):

- Every `rt_cranelift_*` / `spl_cranelift_*` extern in `sffi/codegen.spl` is
  declared with raw `i64` ptr/len params and has NO `text_arg_indices` row in
  `codegen/instr/calls.rs:3132`, so the seed lowering performs no text
  expansion for them; the only expansion is the wrapper's single
  `rt_string_data(x)` / `rt_string_len(x)`. `rt_string_data` is registered as
  `[I64] -> [I64]` (`runtime_sffi.rs:646`) taking the RuntimeValue string.
- That is exactly the "two-arg twin" shape the accepted `fs.spl`
  `rt_io_file_open_read/_write/_append` fix uses (same hand expansion, raw
  `i64` externs, no text row). The `io_file_open` defect needed a *text*
  declaration plus a `text_arg_indices` row (double expansion); the cranelift
  family has neither, so no double-expansion path was found in source.
- Therefore no source change was made. The bug can only be confirmed or closed
  by a seed-built NATIVE run.

Interpreter run of the probe below (seed `bin/simple.exe run`) fails
differently: `spl_cranelift_aot_isa_feature_v2: argument 2 must be an integer`
(interpreter bridge, separate from native lowering); not evidence for this bug.

Why no native red/green on this Windows host (blockers, reproducible):

1. `simple compile probe.spl --native` generates code but the legacy linker
   (`linker/native.rs`) invokes `lld-link` with GNU args (`-o`,
   `--whole-archive`, `-lkernel32`): `lld-link: error: could not open
   '<out>.exe'`. Same with `--linker lld`, llvm-mingw clang first on PATH.
2. `simple native-build probe.spl` (seed) is a whole-project build: needs a
   worker binary (`native_build_worker_binary_valid`, set `SIMPLE_BINARY` to a
   forward-slash path) and then fails with `SCV-E-ADMISSION:
   source-inventory-root-empty: --source root 'src/os'` on a sparse worktree;
   ~8 min per attempt.

Repro to run on a Linux seed (or full checkout):

```spl
use std.nogc_sync_mut.sffi.codegen.{cranelift_new_aot_module_config_v2, cranelift_aot_isa_feature_v2}
fn main():
    val m = cranelift_new_aot_module_config_v2("probe", "x86_64-unknown-linux-gnu", "", 1, ["has_avx"])
    print "avx={cranelift_aot_isa_feature_v2(m, "has_avx")} bogus={cranelift_aot_isa_feature_v2(m, "has_nonexistent_zzz")}"
```

Expect `avx=1 bogus=0`. If the seed-built native binary prints garbage, the
defect is in seed call lowering of `rt_string_data(<text param>)` (not in
`codegen.spl`); write a Rust test in `calls.rs` against that lowering. If it
prints the expected values, close this bug as invalid with that transcript.

## Premise check (2026-11-05, lane p1-common) — downgraded P1 -> P3

The filed mechanism ("call-site lowering re-expands the already-extracted
pointer") requires a text-ABI registry row on the callee. Checked on
`origin/release/1.0.0`:

- `src/compiler_rust/compiler/src/codegen/instr/calls.rs` and
  `src/compiler/50.mir/text_extern_abi.spl` carry **no** row for any
  `rt_cranelift_*` / `spl_cranelift_*` symbol; the wrappers' externs are
  declared with plain `i64` params, so the `rt_string_data(..)` results pass
  through unchanged.
- `rt_string_data` / `rt_string_len` themselves are now listed in
  `tagged_text_value_arg_indices` (parity audit 2026-10-25, after this bug was
  filed), so both producers pass them the tagged text value.
- The accepted `io_file_open` fix in `src/lib/nogc_sync_mut/sffi/fs.spl:321-345`
  uses exactly this manual `rt_string_data`/`rt_string_len` pattern on
  registry-free two-arg twins; the failing form there was the
  registry-listed `rt_io_file_open`.

No seed-built native repro exists. Kept open at P3: close once a seed-built
binary reads back `cranelift_aot_isa_feature_v2` correctly; reopen at P1 with
the transcript if it does not. No code change.

## 2026-11-06 — REPRODUCED (seed hybrid-JIT path), root-caused, fixed in pure Simple

Host: Windows 11, Xeon W-2135, seed `bin/simple.exe` (Rust). Worktree
`work/vector-provider-harden-20261106` on `origin/release/1.0.0`.

### What actually fails

Not the filed mechanism (no double text expansion exists — the 11-03/11-05
static readings were right). The real defect is in the seed's **hybrid-JIT
interp-splice**: under `simple run`, every `rt_cranelift_*` / `spl_cranelift_*`
extern is JIT-unresolvable and lowered to `MirInst::InterpCall`
(`[engine-demotion] reason=hybrid-interp-splice detail=...spl_cranelift_aot_isa_feature_v2,...`).
`compile_interp_call` (`src/compiler_rust/compiler/src/codegen/instr/core.rs:910-940`)
boxes an argument with `rt_value_int` **only when its vreg has a `vreg_types`
entry**; a direct call's result vreg has none (the same function's comment
says so for dests), so `f(rt_string_data(x), rt_string_len(x))` stores the
RAW pointer/length into `argv` and `rt_interp_call` decodes them as tagged
RuntimeValues. The interpreter bridge (`interpreter_extern/cranelift.rs`
`expect_i64`) then rejects them or receives garbage.

Probe (real wrappers, valid config — note the 11-03 repro probe was itself
malformed: the provider requires `cpu == "generic"` and feature names
`sse4.1|sse4.2|avx|avx2|fma`, not `""` / `has_avx`):

```
bin/simple.exe run test/01_unit/lib/nogc_sync_mut/sffi/fixtures/isa_feature_readback_jit.spl
```

Unfixed `codegen.spl` (first run, from an ad-hoc copy of the probe):

```
ERROR rt_interp_call error: Runtime("spl_cranelift_new_aot_module_config_v2: argument 1 must be an integer")
m_nonzero=false opt=-1
ERROR rt_interp_call error: Runtime("spl_cranelift_aot_isa_feature_v2: argument 2 must be an integer")   (x5)
sse4.2=0 avx=0 avx2=0 fma=0 bogus=0
```

(argument indices are 0-based: the LENGTH arg is the one rejected.) The same
fixture unfixed then SEGVs (rc=139) on 4/4 repeat runs — the decode of a raw
word is address-dependent, so the failure is garbage, not a stable value.

Control: binding each expansion to a typed local (`val p: i64 = rt_string_data(f)`)
gives the vreg a type, the splice boxes it, and the identical call reads back
`sse4.2=1 avx=1 avx2=1 fma=0 bogus=-1`.

### Fix (pure Simple)

`src/lib/nogc_sync_mut/sffi/codegen.spl`: all 13 hand-expanded wrappers now
bind `rt_string_data`/`rt_string_len` to typed `i64` locals before the extern
call (ISA family plus `declare_string_data`, `declare_global_data*`,
`function_addr_in_func`, `begin_function`, `get_function_ptr`,
`declare_function`, `emit_object`). `@workaround` tags kept with the corrected
reason, because the seed defect itself is NOT fixed:

**Remaining seed gap (not fixed, needs a seed rebuild):** `compile_interp_call`
should box untyped i64 call-result args for `rt_`/`spl_` bridge targets (or
`vreg_types` should carry call-dest types). Any other Simple code passing an
inline extern call result into a spliced extern hits the same corruption.

After the fix: `module_ok=true opt=2` / `sse4.2=1 avx=1 avx2=1 fma=0 bogus=-1`
(3/3 runs).

### Host CPU readback paths vs CPUID truth (all correct)

C ground truth (`clang` + `<cpuid.h>`): leaf1 ecx=0xffdaf38f edx=0xbfebfbff,
leaf7 ebx=0xd19fffb9, xcr0=0xff → sse4.2 avx fma avx2 avx512f/bw/cd/dq/vl all 1.

- `std.nogc_sync_mut.sffi.cpu` (`cpuid`, `xgetbv`) under seed `run`: identical
  register words (signed i32), xcr0=255, every bit matches.
- `std.nogc_sync_mut.simd.profile` under seed `run`: sse/avx/avx2 true,
  `profile_name()=x86_64_avx512`, width 512.
- C runtime `runtime_simd_dispatch.c` (`rt_simd_has_sse/avx/avx2`,
  `rt_x86_avx512_os_state_usable`): all four equal the CPUID/XGETBV decode
  (new selfcheck below).

Other findings, NOT fixed here:

1. `sffi.cpu.x86_avx512_os_state_usable()` under seed `run` aborts:
   `extern rt_x86_avx512_os_state_usable (argc=0) is declared in Simple but backed
   by no implementation`. The Rust runtime defines it
   (`runtime/src/x86_simd_probe.rs`) but neither the JIT symbol table nor the
   interpreter extern table (`interpreter_extern/mod.rs`, which has
   `rt_cpuid_tuple`/`rt_xgetbv`) registers it.
2. Dual-lane divergence: the Rust seed's `rt_simd_detect_profile` reports 3
   (`x86_64_avx512`) on this host, while the C runtime's
   (`runtime_native.c:5285`) never returns 3, so a native binary reports
   `x86_64_avx2` / width 256 on the same machine. Owner decision whether C
   should report the AVX-512 tier.

### Native path (time-boxed, still blocked on this host)

`simple compile <fixture> --native`: lld-link fed GNU args
(`could not open '<out>.exe'`, unknown `--whole-archive`, `-lkernel32`).
`--linker ld`: bare `ld` with no mingw search paths (`cannot find -lkernel32
... -lc`; `LIBRARY_PATH` is ignored by bare ld). Not pursued further.

### Tests

- `test/01_unit/lib/nogc_sync_mut/sffi/isa_feature_readback_spec.spl` (+ fixture
  `fixtures/isa_feature_readback_jit.spl`). The JIT case shells out with
  `env -u SIMPLE_EXECUTION_MODE -u SIMPLE_RUNTIME_MODE` — the runner exports
  interpreter mode, and a child inheriting it passes vacuously (the precedent
  `erased_receiver_index_of_bind_spec.spl` likely has the same hole).
  `SIMPLE_SPEC_COMPILER=bin/simple.exe bin/simple.exe test <spec>`:
  unfixed 3 passed / 1 failed (the JIT case); fixed 4/4 passed.
- `src/runtime/test/rt_host_isa_cpuid_parity_selfcheck.c`: `PASS: host ISA
  readback equals CPUID/XGETBV truth (4 predicates)`.

Status: premise (garbage ISA readback) CONFIRMED on the seed `run` path and
fixed at the Simple wrapper layer; seed `compile_interp_call` boxing gap stays
open. Native seed-built red/green still not obtained.


## Round 15 note (2026-11-07, work/r15-stdlib-20261107)

Prevention: test/01_unit/lib/nogc_sync_mut/sffi/codegen_text_expansion_prevention_spec.spl (no inline rt_string_data/len inside a call; @tag:phase3). Native confirmation still needs a seed-built native binary: verification-pending.


Round 15 verdict update (coordinator cross-check): fixed on release in 2b67a60c222 (2026-11-06). The static prevention spec above stays.
