# Tree-wide POSIX-shell spawn gaps and seed process debt (2026-09-19 sweep)

Date: 2026-09-19
Lane: suite-2026-09-18 (Windows, seed binary)

## Environment-blocked specs (POSIX-only fixtures/spawns on the Windows seed)

1. `src/lib/nogc_async_mut/mcp/fileio_server.spl:380-398` — read/write/
   delete/copy/move/append shell out to `cat`/`echo>`/`rm`/`cp`/`mv`.
   Blocks 12 examples of `test/01_unit/app/mcp/fileio_main_spec.spl`.
   Fix direction: native rt_* file probes (same treatment io_runtime.list_dir
   received in 5476c365f98).
2. `src/app/mcp/main_lazy_ctx_tools.spl:753,923` — ctx batch/execute spawn
   `/bin/sh`. Blocks 3 ctx_batch_scale, 2 token_stats, 6 ctx_tools examples.
3. devhub cmd_github (19 fake-binary examples), cmd_tasks (22), email_cmd
   (13) — `#!/bin/sh` stub binaries cannot exec on the Windows seed
   (extensionless scripts and .cmd shims both fail; the sources spawn the
   tools directly so there is no interpreter seam).
4. Child-process specs running `bin/simple.exe <subcommand>`: ledgered in
   check_worker_seed_interpreter_gap_2026-09-19.md.

## Seed runtime debt (affects any spec doing process spawns)

- `process_run` / `process_run_bounded` execute the child command TWICE and
  return the second result (both `unsafe` lanes fire). Worked around in
  devhub/wiki_git.spl with double-run tolerance; the runtime fix belongs in
  the process facade layer.
- `me` and `case` are reserved words on this seed (specs using them as
  identifiers fail to parse).
- String literals process backslash escapes; Windows paths in specs must use
  forward slashes.
- s[i]/char_count() are char-based while len()/slices are byte-based on the
  seed — multibyte indexing code must walk char arrays (fixed in
  src/app/devhub/convert_storage.spl; SAME BUG still present in
  src/app/itf/convert_storage.spl).

## Production gaps found while triaging

- `src/app/cache_gateway/{gateway,main,publish}.spl` import
  `compiler.driver.cache.remote.namespace_policy` — the module file was
  never committed (squash-merge e274cd33719 added the imports). HEAD does
  not compile the cache_gateway app.
- Commit 81cc36a0048 dropped ponytail ladder mode, diff input, and
  memo/telemetry wiring without updating specs (specs re-pinned in
  12bd321c239). Decide separately whether to restore the wiring.

## Merge e274cd33719 regression pattern

The "merge all share-history worktree branches" commit repeatedly resolved
conflicts by taking pre-triage versions, clobbering 82bf2cfe907 (llm_caret
repairs — restored in 1c3a87982e3) and aff29a24dfe (llm_runtime vllm
support — restored in 0ea76a026ac) plus doc_coverage oracles. Other repairs
from those commits may still be missing; when a spec pins behavior that
used to pass, diff against those commits first.
