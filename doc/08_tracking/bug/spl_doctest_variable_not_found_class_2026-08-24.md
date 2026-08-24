# SPL doctest class `semantic: variable X not found` — triage 2026-08-24

Status: PARTIALLY FIXED (net family green); residue below is real and open.

## Verdict: NOT a harness artifact

The class was replicated **outside** the test runner using the harness's own
`extract_doctests` + `build_spl_doctest_code` (probe dumped 319 composites for
the 92 failing files, each run directly through the seed). The class reproduces
byte-for-byte, so it is not extractor damage of the `6c178bf4a30` kind.

Counts (both correct, different denominators):
- 33 — class map, *first* reason per failing block.
- 63 — this triage, *any* occurrence per composite.

## Cross-tree stdlib reads: real, but REFUTED as the cause

strace of a composite in `/mnt/data/tmp` shows resolution is cwd-first
(805 opens under the lane worktree) with a compiled-in fallback to
`/mnt/data/worktrees/seed-deploy-1`; **92 of those fallback opens succeed**
(runner-infrastructure modules: `spec/*`, `io_runtime`, `process_ops`,
`file_ops`). Real cross-tree contamination, worth its own fix, but it does not
explain this class: the missing symbols exist in *no* tree.

## Sub-class C — not a doctest defect at all (2 blocks)

`src/compiler/15.blocks/blocks/error_helpers.spl` fails **source-alone**
(`./bin/simple <file>` with no doctest appended) with
`error: semantic: variable \`i64\` not found`. Blocks L28/L80 merely inherit it.
Of the 92 failing files, 7 fail source-alone; 2 of those with this message.

## Sub-class A — missing `use` in later doc blocks (FIXED for net)

A module docstring's first fenced block carries the imports; later blocks reuse
the types without re-importing, and each block compiles independently.

Fixed in this change (`src/lib/{gc_async_mut,nogc_async_mut,nogc_sync_mut}/net/__init__.spl`,
blocks at lines 262/296/317/344/359): added the missing `use` and wrapped each
block in a named example function, because these blocks perform live network
I/O at top level and can therefore never pass as *executed* doctests — compile-
checked is the honest contract for a usage illustration. Verified:

    ./bin/simple test --spl-doctest src/lib/nogc_sync_mut/net/__init__.spl
    SPL Doctest: 13 passed, 1 failed, 0 skipped      (was 5 of these blocks failing)

The 1 remaining failure is a different class (`unknown extern function: url_parse`).

## OPEN — documented APIs that do not exist (aspirational docs)

These blocks cannot be fixed by an import: the symbol exists nowhere in the tree.
Fixing them means implementing the API or rewriting the docs against the real one.

| symbol | doc file(s) | reality |
|---|---|---|
| `CompressionLevel`, `GzipCompressor` | `src/lib/{gc_async_mut,nogc_async_mut,nogc_sync_mut}/compress/__init__.spl` L98/L152 | module is a docstring-only stub; none of the documented submodules or types exist |
| `SocketHandle`, `JoinSet` | `src/lib/nogc_async_mut/async_host/__init__.spl` L137/L173 | defined nowhere |
| `Promise` | `src/lib/nogc_async_mut/async/__init__.spl` L177 | exists only in `js/` and `common/testing`, not the async family |
| `pipeline.add(...)` | `http_server/{cors,csrf,access_log,rate_limit,request_validation,security_headers}.spl` | `MiddlewarePipeline` exists (`http_server/middleware.spl:50`) but has no `add` method |

## OPEN — fragment blocks (undefined locals)

`request`, `socket_fd`, `config`, `data`, `body`, `repo`, `user`, `actions`,
`api_routes`, `future`, `runtime`, `file`, `token_string`, `static_handler`,
`db_health_check`, `access_log_handler`, `query_text`, `name`, `response`.
Each starts mid-scenario. The fix is a typed example function taking the value
as a parameter — but for the `http_server` cluster that immediately surfaces the
missing-method row above, so it is blocked on the same API gap.

`src/lib/nogc_sync_mut/io/buffer.spl` L16/L25/L39 need
`use std.io.file.{FileHandle, File}`; adding it resolves `FileHandle` but the
blocks then hit `FileHandle.read_file(path)` / `.create(path)` signatures the
real `io/file.spl` does not provide — another API-vs-doc mismatch, left for the
owner rather than patched into a different-looking failure here.
