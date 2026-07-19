# Seed interpreter: memory accumulates across parse_module calls (~30 MB/file) — long probe runs hit multi-GB RSS

- **Status:** open (seed/Rust interpreter; worked around by chunking probe runs)
- **Date:** 2026-07-03
- **Component:** `src/compiler_rust` interpreter (memory retention across calls),
  observed driving `src/compiler/10.frontend/core` `parse_module` under
  `src/compiler_rust/target/bootstrap/simple run`

## Symptom

A single interpreter process that calls `parse_module` over many files grows
RSS monotonically — roughly 30-35 MB per average source file — and never
releases it between calls. A one-process sweep over the 245-file stage4 parse
set crossed a 4 GB cgroup cap (`scripts/resource/run_capped.shs`,
`CAP_MEM_MAX=4G`) at file 118 (`src/compiler/frontend/core/lexer.spl`) and was
killed (exit 137).

This is cumulative, not per-file: parsing the "killer" file alone in a fresh
process completes well under the cap. Each earlier kill point is just where
the running total crosses the cap.

The 2026-07-03 host OOM previously attributed to parsing
`tmp_probe/imp_d.spl` was a separate issue: that file (in worktree
`agent-a852460048b5c9bcf`) is a physics probe with `while i < 60:` and no
increment — an infinite allocation loop when *executed*, not a parser bug.
Parsing it is bounded.

## Repro

```bash
CAP_MEM_MAX=4G scripts/resource/run_capped.shs env RUST_LOG=error \
  src/compiler_rust/target/bootstrap/simple run src/app/test/parse_probe_all.spl
# killed by the cap partway through parse_set.txt (245 files);
# any single file from the set parses fine in a fresh process.
```

## Workaround

`src/app/test/parse_probe_all.spl` accepts `PARSE_LIST=<chunk file>`; run the
set in ~60-file chunks, one fresh capped process per chunk.

## Suspected cause

Interpreter global/module state retained per `parse_module` invocation (AST
node arenas addressed by global counters, lexer `lex_state_get/set` string
state, interned strings) is never freed; the stage4 parser stores AST nodes in
global tables that only grow. Fix direction: either interpreter-level release
of dead heap between top-level calls, or a `parser_reset()`/arena-reuse hook
in the stage4 parser.

## 2026-07-17 native Stage4 evidence

The same retention shape was reproduced in a no-GC pure-Simple Stage4 process.
`ast_reset`, `expr_reset`, and `stmt_reset` replaced every flat arena array for
each parsed module. They now allocate only for native zero initialization and
otherwise clear and reuse backing storage. At 157 parsed modules, maximum RSS
fell from about 9.3 GiB to 7.9 GiB (about 15%) in like-for-like runs.

The remaining slope correlated with bootstrap expression/statement setters
mirroring roughly ten and six environment variables per node respectively.
Native Stage4 now makes the flat arrays authoritative, gates those mirror
writes, keeps node counts in local slots, and ignores stale per-node environment
keys. The aggregate AST modules pass the bootstrap compile gate. Full Stage4
memory and executable verification remains open and is intentionally deferred
after the third bounded retry.

## 2026-07-19 regression restoration

Parallel work later replaced the arena-reuse resets with fresh `[]` allocations
and re-enabled expression/statement env mirrors under native Stage4. The
measured fix is restored against the current arena schema, including flat
declaration bodies, trait metadata, and mutable-parameter markers. This restores
the earlier ~15% improvement only; the no-GC runtime's process-lifetime object
registry still needs a parse-owned scratch allocation domain for full closure.
