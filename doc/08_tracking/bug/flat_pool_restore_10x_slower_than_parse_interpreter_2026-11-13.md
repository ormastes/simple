# Interpreter lane: restoring flat pools from a cache blob costs ~9-10x a fresh parse (2026-11-13) — FIXED

**Binary:** `/home/yoon/dev/simple/src/compiler_rust/target/bootstrap/simple` (Rust seed,
119570696 bytes, 2026-11-05 18:12), `simple test` lane, shared box (load ~8), worktree
`simple-nodestore-20261113`.

**Measurement** (`src/compiler/00.common/data/data_schema_resolver.spl`, 514 lines, 1,973 AST
nodes, one process, `rt_time_now_unix_micros`):

| step | us |
|---|---|
| fresh parse + bridge (`parse_and_build_module_scoped`, capture armed) | 10,445,476 |
| `.fpc` line-blob hit (`build_module_from_flat_pool_blob`) | 94,907,795 |
| packed encode (`flat_packed_encode_refs_v1`) | 15,055,089 |
| packed view validation (`flat_packed_view_v1`, in memory) | 2,725,420 |
| packed hit build (`build_module_from_packed_view_v1`) | 99,931,338 |

Both restore formats cost ~9-10x the parse they replace, and the cost is in the pool restore +
bridge, not in validation (2.7 s). On this lane a cache hit is therefore a slowdown, and the AST
pool snapshot (node-storage phase C) inherits it: materialising a module costs ~10x reparsing it.
The native lane, where `.spab` is the default hit format, has not been measured here.

**Suspect.** Per-element pool rebuild through immutable array growth in
`flat_*_pools_restore` (`FlatPoolReader`), quadratic under the interpreter's copy-on-push
arrays. Next step: time `flat_pools_restore_reader_v1` alone vs the bridge
(`flat_ast_to_module`) on the same module, then fix the dominant term.

## Resolution (`e333c37af8f`)

Not the pool restore: `lex_source_byte_offset`'s char->byte cursor rewound to 0 on every
backward query, and a cache hit (lexer on the real non-ASCII module) converts spans out of
source order, so it paid an O(n) walk per span; a fresh parse only looked cheap because its lexer
was left on a short interpolation fragment
(`fresh_parse_vs_cache_hit_span_divergence_2026-11-13.md`). Replaced by a per-source prefix
table. Same module, same binary: packed materialise 103.8 s -> 10.6 s; fresh parse now 7.5 s in
that run (6.2-6.4 s in the 3-rep probe).
