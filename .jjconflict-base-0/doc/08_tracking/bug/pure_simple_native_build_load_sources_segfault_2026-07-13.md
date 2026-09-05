# Pure-Simple native-build crashes while loading sources

## Status

Runtime ABI defects through `rt_path_join` are fixed and covered by the shared
core ABI probe. Stage 13 reaches native-build cache path construction, but an
updated pure-Simple compiler could not be produced in stage 14 because all
three bounded seed/worker entry variants stalled before native object discovery.
Cross-compiled runtime binaries pass on x86-64, AArch64, and RV64GCV; updated
Simple/LLVM AOT execution evidence for the Engine2D SIMD row scheduler remains
blocked on the bootstrap-dispatch stall.

## Reproducer

```sh
build/bootstrap-simd-stage4/simple native-build \
  --source test/fixtures/compiler --source src/lib --entry-closure \
  --entry test/fixtures/compiler/llvm_simd_row_native_probe.spl \
  --backend llvm --target x86_64-unknown-linux-gnu --mode one-binary \
  --cache-dir build/check/simd-row-stage4-x86-cache \
  --output build/check/simd-row-stage4-x86
```

Observed on 2026-07-13: exit 139 with no compiler diagnostic. The independent
`build/bootstrap-simd-stage3/simple` artifact fails identically.

## Backtrace

```text
SIGSEGV
CompilerDriver.load_sources_impl
CompilerDriver.compile
compiler_driver_run_compile
cli_native_build
main
```

The next fix should make `load_sources_impl` return a source-loading error
instead of dereferencing an invalid module/source handle. Do not use the Rust
seed as production evidence or retry bootstrap loops to bypass this crash.

## Bootstrap rebuild evidence

On 2026-07-13, three bounded attempts used the optimized Rust seed only to
rebuild the pure-Simple CLI with the concrete entry
`src/app/cli/_CliMain/main_and_help.spl`, `--entry-closure`, and the preserved
1,177-object cache. Each attempt timed out after 900 seconds before discovery
or object generation, at about 100% CPU and 1.27 GB RSS. Using one
`--source src` root instead of the three compiler/app/lib roots did not change the
result. With `SIMPLE_NATIVE_BUILD_RUST_TRACE=1`, the final attempt recorded
zero `discover visit` events, zero cache mutations, and no output artifact.

The first attempt exposed invalid nested-JSON brace escaping in
`src/app/stats/doc_coverage_dynamic.spl`; that source now passes the focused
bootstrap check. After that repair, the final build log contained zero parser
errors but still timed out before discovery. The remaining investigation must
instrument the pre-discovery source-analysis phase rather than retry the same
full CLI build.

Follow-up identified the dispatch cause: a host `native-build` without
`--target` is a pure-Simple tool and interprets `src/app/cli/native_build_main.spl`;
it never enters the Rust bootstrap builder. Supplying the real host target
`--target x86_64-unknown-linux-gnu` routes the seed to its bootstrap handler and
starts entry discovery in seconds. That path then exposed a spanless Rust-parser
failure in `src/lib/common/encoding/sfnt.spl`; discovery now reports parser
line/column, and a focused regression covers the compatible SFNT source form.

## Stage-5 evidence

An explicit host target completed the optimized Rust-seed bootstrap build in
244.2 seconds: 1,019 reachable files compiled, zero failed, and
`build/bootstrap-simd-stage5/simple --version` reports `Simple v1.0.0-beta`.
The stage-5 artifact reaches pure-Simple native-build, but the SIMD probe then
reported `function not found: str.split_lines` and exited 139. `split_lines`
is implemented by the Rust interpreter but is absent from native method
registration; `split` lowers to `rt_string_split`. The entry-closure scan now
uses one `content.split("\\n")` pass, preserving the linear scan while using
the supported native ABI.

## Stage-6 through stage-8 evidence

The cache-preserving stage-6 rebuild compiled 3 files, reused 1,016 cached
objects, and linked in 146.2 seconds. Its first native SIMD probe reached
`CompilerDriver.load_sources_impl`, where disassembly identified a null call
through the declared but C-runtime-missing `rt_array_concat` ABI.

The shared C runtime now implements `rt_array_concat` for generic, packed-byte,
packed-u64, and mixed arrays without mutating either input. The existing core-C
ABI probe covers those cases, invalid input, and the exported symbol. That
focused probe passes. Stage 7 then compiled 2 files, reused 1,017 cached
objects, and linked in 155.0 seconds. Its next null call was `rt_array_clear` from
`expr_reset`; the C runtime now implements the same validate-and-reset behavior
as the Rust and simple-core runtimes, with valid and invalid cases in the ABI
probe.

Stage 8 compiled 2 files, reused 1,017 cached objects, and linked in 137.6
seconds. `nm` confirms both `rt_array_concat` and `rt_array_clear` are defined.
The pure-Simple LLVM SIMD probe still exits 139 before emitting a compiler
diagnostic. A bounded debugger run located the fault in
`compiler.frontend.core.lexer.lex_init_with_path`: the native global for
`lex_env_save_enabled: [bool] = [false]` remained zero and the trusted inline
`rt_array_len` path dereferenced that zero value.

The Rust HIR constant-array collector did not accept boolean expressions, so it
discarded `[false]` instead of emitting module initialization. Both native
backends now preserve boolean constant arrays and box each element with
`rt_value_bool`; scalar `false` uses the canonical tagged value 19 instead of
nil 3. The shared `UnboxInt` lowering, which also handles native boolean array
elements, recognizes tagged true/false and returns raw 1/0. Trusted inline
array length lowering in Cranelift and LLVM now also honors the runtime ABI's
`rt_array_len(nil) == 0` contract. Focused JIT and native compile-and-run
regressions cover the boolean initializer and nil length cases, and the LLVM
feature path compiles successfully.

Stage 10 then reached `make_core_lexer` and called a zero GOT entry for
`rt_string_chars`, which was declared by codegen but absent from the shared C
runtime. The C and simple-core runtimes now implement the ABI with UTF-8
character boundaries, and empty-delimiter string splitting reuses it. The
core-C ABI probe covers ASCII and multibyte output. Stage 11 compiled 2 files,
reused 1,017 cached objects, and linked in 133.8 seconds; its probe passed both
former null calls and reached source parsing.

The remaining stage-11 failure classifies all source keywords as identifiers:
the parser consequently reports every function `->` and block `:` as an
unexpected expression token, then performs a nil field access and terminates
with `SIGILL`. A direct pointer-as-`i64` ABI fixture produced the same result,
so typed `[u32]` signatures are not the cause and the production fixture was
left unchanged. The mandatory third-cycle cap stopped further rebuilds. The
next continuation should trace `keyword_lookup(ident_text)` and the
`source_chars[start:pos].join("")` token text produced by the core lexer, then
prevent AST construction after parser errors.

## Stage-12 and stage-13 evidence

The stage-11 keyword failure came from the C runtime's string-only `rt_slice`:
the core lexer stores `source.chars()` as `[text]`, then reconstructs an
identifier with `source_chars[start:pos].join("")`. Array slicing returned nil,
joining nil returned nil, and every `keyword_lookup` comparison therefore
fell through to `TOK_IDENT`. C and simple-core `rt_slice` now support arrays;
the core-C ABI probe reconstructs `"fn"` through the exact chars/slice/join
path. A lower-model sidecar independently traced and confirmed this cause.

Stage 12 compiled 1,022 files and linked in 236.4 seconds. Its LLVM probe
produced no parser errors and reached HIR/MIR lowering, where a minimal
`return 0` program exposed another zero call: C `rt_is_none` was missing even
though codegen and simple-core expose it. The C runtime now implements the
same nil/None-enum semantics as simple-core, and `rt_is_some` delegates to it.

Stage 13 compiled 2 files, reused 1,020 cached objects, and linked in 133.0
seconds. The minimal LLVM build passed frontend and MIR lowering, then reached
`driver_native_build_cache_scope` and called a zero GOT entry for
`rt_path_join`; `nm` reports `U rt_path_join`. Rust and simple-core implement
the four-argument raw-text ABI, but the C runtime does not. The third-cycle cap
stopped further fixes/rebuilds. The next continuation should add C
`rt_path_join` with path-join ABI coverage, rebuild from the preserved cache,
prove the minimal program, and then rerun the unchanged SIMD probe.

## Stage-14 evidence

The C runtime now implements the four-argument raw-text `rt_path_join` ABI with
the same valid-input, byte-oriented POSIX behavior as simple-core: an absolute
right path replaces the left path, empty sides copy the other side, and
relative paths gain exactly one separator. The shared core ABI probe covers
relative, absolute, empty-side, and trailing-separator joins; its core-C lane
passes, and the same source runs against simple-core when an ABI-complete archive
is available. A fresh bootstrap-profile Rust seed/runtime build also passes.

Three bounded pure-Simple rebuild variants were attempted with the preserved
`build/bootstrap-simd-stage5/cache`: direct `native-build`, the dedicated
`native_build_main.spl` entry, and direct `native-build` after refreshing the
seed with `SIMPLE_BOOTSTRAP=1`. Each loaded the Simple compiler graph, then
stalled before native object discovery at about one CPU core and 1.22-1.27 GB
RSS. No output binary or new cache object was produced, so each attempt was
terminated rather than waiting for the redundant 900-second timeout. The
mandatory three-cycle cap prevents another rebuild in this session.

The next continuation should diagnose why current seed dispatch no longer
reaches the cached native-build worker path that produced stages 12 and 13.
Keep `build/bootstrap-simd-stage5/cache`, do not rerun an unchanged entry path,
and resume the unchanged LLVM SIMD probe only after a new pure-Simple compiler
artifact is produced.
