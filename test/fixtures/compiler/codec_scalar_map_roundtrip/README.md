# Integer dictionary codec native probe

Status: authored, independently ACCEPT_STATIC; compilation and execution UNRUN.

Standalone entry: `main.spl`. Uses the actual generated `hc_enc_scope`,
`hc_dec_scope`, `hc_enc_symbol_table`, and `hc_dec_symbol_table` through
`compiler.hir.generated.hir_codec`, with `HirCodecWriter`,
`FlatPoolReader`, and public `Scope`/`SymbolTable` models. No SSpec runner,
frontend parser, HIR lowering, Rust seed, or mocked codec is invoked.

Checks all seven affected maps with -1, 0, 1, 2, 3, 4 and signed i64 extrema;
checks keys, cardinalities, actual scalar values, reader completion, node
scope preservation and byte-identical re-encoding. Both canonical and legacy
readers must reject N, noncanonical 03/+3, and truncated value tokens without
inserting zero. A direct typed parse/insertion control runs first.

The compilation closure still includes the whole generated HIR codec and its
reachable HIR models, codec support, flat-pool reader, and runtime facilities.
It is smaller by entry purpose than the compiler driver, but no closure size
or build-time claim has been measured.

Compile only through the root-coordinated admitted d85 native-build procedure,
with canonical source/runtime binding, no stub fallback, isolated cache/output,
and current campaign memory/time limits. Runtime execution is required after
successful compilation. The four printed milestone lines identify which real
assertion group completed; output presence alone is not a pass without exit0.

The probe compiles patched generated codec source into its own executable. It
does not change the admitted compiler binary or establish that all22 v5 cache
refusals have this cause. Production integration needs a new admitted producer
and preserved full-module codec/cache self-checks.
