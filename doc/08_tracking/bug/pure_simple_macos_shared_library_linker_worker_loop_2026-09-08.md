# Pure-Simple macOS shared-library link fails in linker selection/runtime closure
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Status

Linker fixes implemented and bootstrap-diagnostic dylib produced; end-to-end
admission remains blocked on a source-matched self-hosted compiler.
The selected Chromium primitive-oracle prerequisite remains blocked until that
build and its native ABI integration gate pass. No dylib is currently admitted
or retained as successful evidence.

## Reproduction

```text
bin/simple compile tools/chromium-primitive-oracle/chromium_primitive_oracle.spl \
  --native --shared --strip \
  -o build/chromium-primitive-oracle/libsimple_chromium_primitive_oracle.dylib
```

The default path invokes `ld.lld`, which rejects Mach-O `main.o` and runtime
archive members as unknown/non-ELF files and cannot find `-lSystem`.

An explicit macOS target and system linker reaches Mach-O linking:

```text
bin/simple compile tools/chromium-primitive-oracle/chromium_primitive_oracle.spl \
  --native --shared --strip --target aarch64-apple-darwin --linker ld \
  -o build/chromium-primitive-oracle/libsimple_chromium_primitive_oracle.dylib
```

It then fails because `libsimple_runtime.a(runtime_thread.o)` references the
undefined symbol `_worker_loop_entry`. The bridge does not use threads directly;
the shared-library runtime closure nevertheless retains `runtime_thread.o`.

## Implemented correction

`src/runtime/runtime_thread.c` now declares the optional Simple worker entry as
Darwin `weak_import` while retaining ELF `weak` semantics elsewhere. Compiling
that runtime source as a Mach-O object reports `_worker_loop_entry` as
`(undefined) weak external`, so an omitted thread-pool module no longer creates
a required dylib dependency. The full Chrome bridge build was not repeated in
this session because its three-attempt verification cap had already been
reached before this root cause was corrected.

The later diagnostic build exposed two additional generic linker defects and
corrected them in `src/compiler_rust/compiler/src/linker/native.rs`:

1. macOS target-aware detection now selects Apple `ld` instead of ELF
   `ld.lld`, failing closed if Apple `ld` is unavailable;
2. Darwin shared plugins use `-undefined dynamic_lookup` so their runtime calls
   bind to the loading Simple process rather than requiring a duplicate runtime.

Focused tests for both policies pass. A bootstrap-only diagnostic build now
produces an arm64 Mach-O dylib with the five frozen ABI exports. It is named
`libsimple_chromium_primitive_oracle.bootstrap-diagnostic.dylib` and is not
admission evidence.

## Independent compiler-build result

An independent self-hosted compiler build subsequently ran for 3654 seconds
and reached LLVM code generation, but produced no executable. It failed in the
VHDL plugin set because builtin string-method calls could not be resolved:
`str_len`, `str_contains`, and `str_starts_with`. Maximum RSS was approximately
3.9 GB. This is upstream of the shared-library acceptance run, so the corrected
Darwin weak import remains object-level evidence rather than an admitted dylib.

The canonical-looking `bin/release/aarch64-apple-darwin/simple` is not an
alternative: it identifies itself at runtime as a Rust bootstrap seed and its
older command parser rejects the current shared-library invocation before
reading the source. No probe dylib was produced, so this path is excluded from
Chrome-library evidence.

## Expected

On Darwin, `--shared` selects a Mach-O-capable driver/linker and links only the
runtime closure required by the Simple module, or supplies every retained
runtime symbol. The output dylib must contain the five requested C exports.

## Acceptance

1. The reproduction succeeds using an admitted self-hosted Simple compiler.
2. `file` reports a Mach-O arm64 dynamically linked shared library.
3. `nm` exposes exactly the five `simple_chromium_oracle_*` ABI symbols plus
   explicitly documented Simple runtime initialization symbols.
4. The native ABI integration test loads, invokes, and exact-once releases it.

