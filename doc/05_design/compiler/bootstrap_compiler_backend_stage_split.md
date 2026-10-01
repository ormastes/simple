<!-- codex-design -->
# Bootstrap compiler/backend stage split detail design

The four stage identities are fixed: Stage 1 is the Rust-built seed; Stage 2
is the unchanged canonical pure-Simple Stage-2 compiler build; Stage 3 is the
unchanged canonical pure-Simple Stage-3 compiler build; and Stage 4 is
tools-only with zero compiler-source compilation.

Stage 2 preserves the existing canonical pure-Simple compiler configuration
and publishes its receipt. Stage 3 preserves the existing canonical
pure-Simple compiler configuration, consumes that exact receipt, and atomically
publishes the compiler
executable, compiler-core archive, public interface manifest, runtime archive,
and provenance manifest.

Stage 4 resolves only approved tool/app modules and non-compiler libraries.
Compiler imports bind to the Stage-3 interface/archive. Discovery fails if a
compile unit is rooted under `src/compiler` or an imported symbol is absent.
Linking verifies all archive and interface hashes.

`RuntimeRequiredSymbolsV1` contains the sorted, duplicate-free symbol names,
runtime archive hash, target, ABI, producer, and manifest hash. Publication
rejects an empty roster or duplicate symbol. Stage 4 resolves every row against
the admitted archive before link; a missing row returns
`missing-required-runtime-symbol:<name>`. Link logs containing hosted fallback,
generated runtime stubs, or unresolved-symbol fabrication fail admission.
Only after link and `ToolingLinkReceiptV1` validation may the exact output run
bounded `--help` and `--version` probes.

Required counters: Stage-2/3 compiled files, Stage-4 tool files,
`stage4_compiler_files` (zero), reused bytes, elapsed time, peak RSS, and final
hash. Migration requires a legacy admitted baseline. Behavioral equivalence is
then checked by a separately invoked audit/full-rebuild command; that command
is never part of Stage 4.
