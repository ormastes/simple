# Ordinary parser statements allocate unused contract snapshots

Status: isolated source fix and focused native regression prepared; execution and absolute performance acceptance pending.

## Source defect

At source `403a5409fbc65aef59f4f23dd8edd7a465ea721f`, every `parse_statement()` invokes `try_parse_contract_stmt()`. The latter creates a lexer snapshot and a parser-token snapshot before reading the current token/name to decide whether it could begin a contract. For ordinary `val`, `var`, return, and expression statements, the name test fails without advancing the lexer.

`lex_snapshot_save()` creates numeric/text arrays and copies the indentation stack. `parser_tok_save()` creates another numeric array. On the ordinary miss, `lex_snapshot_commit()` releases the lexer arrays, while the unused parser-token numeric array is not explicitly released. These operations are unnecessary for classification. They add constant per-statement allocation work, an indentation-depth copy, and retention until the applicable owner/scope reclaims the parser array; this is not proof of quadratic whole-file parsing.

The fix moves both snapshot calls after the recognized-name test, immediately before the first `parser_advance()`. Recognized contracts and ambiguous prefixes retain their existing snapshot, rollback, and commit paths. The miss still returns `-1` without changing token state. No user grammar, AST representation, trace policy, or cache authority changes.

## Focused regression

`test/05_perf/compiler/parser_contract_miss_allocations.spl` is a native fixture against the patched parser. It verifies 64 repeated ordinary misses preserve token kind/text/line/column and lexer offsets, normal token advancement still reaches the binding, `out(stable)` rolls back to an ordinary call, and a real `proof uses` clause retains its node kind/name.

It reports the actual C owner `rt_heap_registry_count()` before/after warmed misses. This includes all registered objects, not only arrays. No unmeasured zero-allocation budget is asserted. The historical `rt_heap_array_capacity_bytes` symbol is absent from the retained C runtime and is deliberately not used. Native compilation/execution remains pending; do not substitute the interpreter or label the fixture green without its verdict.

## Observed slow build and limits

The retained Windows producer SHA-256 is `83a7f5f163c27308c8d2c35748dac75af0f210dcd62f51998ff2e8d5f6493668`. A runtime fallback component build timed out at 902.625 seconds after parsing 22/35 files. `process_ops.spl` (106865 bytes) took 481678 ms wall time; `host_path.spl` (8076 bytes) took 148720 ms. The run enabled `SIMPLE_COMPILER_TRACE=1` and wrote 147068 stderr lines. Contemporaneous host I/O pressure was high. No paired per-file CPU measurement exists.

Evidence: `D:/dev/simple-windows-host-owner-fix-20260929/runtime-cache-windows-native-fallback-cycle2/review-result.md` and its preserved logs. The allocation defect is established by source control flow; its contribution to that timeout is unmeasured. One separately reviewed tiny trace-off/on diagnostic is being prepared. The failed full build is not repeated.
