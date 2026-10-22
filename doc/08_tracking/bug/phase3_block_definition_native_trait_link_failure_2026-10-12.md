# Phase 3 block definition native trait link failure

Attempt 7 is terminal with exit 1 at frozen source
`ca45950aefb301add31a0632c0c9fd8cba4d505a`. The actual seed-produced native
Stage2 build rebuilt 1,272 modules, reused zero, and failed to link these three
symbols referenced by `blocks.mod.block_info`:

- `src__compiler__blocks__blocks__definition__BlockDefinition.description`
- `src__compiler__blocks__blocks__definition__BlockDefinition.lexer_mode`
- `src__compiler__blocks__blocks__definition__BlockDefinition.syntax_features`

The authoritative log is
`C:/dev/simple-phase3-attempt7/build/bootstrap/logs/x86_64-pc-windows-msvc/stage2-native-build.log`,
SHA256 `ee7d39f8571d5c1d15e7b8f81bfeaab12fe3a8e7ad94b7f58d9bb99b5960ae9c`.
Its adjacent RSS receipt reports complete measurement, exit 1, quiescent 1,
zero observer errors, and peak 1,363,148 KiB under the unchanged 5,859,375 KiB
compiler cap. This is the seed-produced native build measurement; it proves
no improvement in the previously failing full CLI HIR workload. All 23
dependent native probes are blocked upstream, with zero executions.

## Source repair

The concrete block owners used unsupported `struct Owner(BlockDefinition)`
syntax and inherent methods. The native trait implementation collector consumes
actual trait implementation records. The repair uses plain structs and explicit
`impl BlockDefinition for Owner`, keeping constructors in their inherent owners.
It also repairs the trait's lexer and optional result annotations to name the
actual result types used by its implementations.

MIR now retains the declared trait identity across live enum-match value edges
and selects the existing native trait dispatch ABI before legacy direct-call
resolution. Distinct implementations and default-method overrides must remain
visible through the registry; three constant/default replacements would not
repair this behavior.

The changes are integrated in preparation attempt 8 as
`ac6c0a021c5bf2c94c798a2ed3e597bd8467e2eb` and
`2fd1573f4653814bb83344283736c410ec88475a`. A reproducible external source audit
compared every indented method body in all seven block files against the exact
pre-migration parent. All 138 bodies are unchanged, including 118 concrete-owner
bodies and 20 trait defaults. This is source parity, not execution evidence.

## Required qualification

The native fixture `test/fixtures/compiler/native_trait_match_owner.spl` has six
assertions covering imported implementations with different layouts, optional
match and guarded arms, nil early returns, defaults and overrides.
`test/fixtures/compiler/native_block_registry_trait_metadata.spl` has 47
assertions covering all eight built-in registrations, padded custom metadata,
actual parser behavior, duplicate registration, removal and default metadata.
Neither fixture has compiled or executed under an admitted attempt 8 compiler.

Closure requires the next exact compiler to link, compile and run Hello, then
compile and execute both fixtures with their expected positive assertion
receipts. The complete CLI/runner/MCP/LSP and bounded-memory qualification remain
separate mandatory work. This bug remains open until that evidence exists.
