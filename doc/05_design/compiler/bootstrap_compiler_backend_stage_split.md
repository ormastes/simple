<!-- codex-design -->
# Bootstrap compiler/backend stage split detail design

Stage 2 selects Cranelift and publishes a pure-Simple compiler receipt. Stage 3
consumes that exact receipt, selects LLVM, and atomically publishes the compiler
executable, compiler-core archive, public interface manifest, runtime archive,
and provenance manifest.

Stage 4 resolves only approved tool/app modules and non-compiler libraries.
Compiler imports bind to the Stage-3 interface/archive. Discovery fails if a
compile unit is rooted under `src/compiler` or an imported symbol is absent.
Linking verifies all archive and interface hashes.

Required counters: Stage-2/3 compiled files, Stage-4 tool files,
`stage4_compiler_files` (zero), reused bytes, elapsed time, peak RSS, and final
hash. Migration requires a legacy admitted baseline plus tooling-only/full-build
behavioral equivalence.
