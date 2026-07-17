# Stage4 entry closure parses duplicate sources and exceeds bounded runtime

**Date:** 2026-07-17  
**Status:** OPEN  
**Owner:** compiler driver entry-closure source collection

## Evidence

The pure-Simple Stage3 binary `stage3-generic-close` started an exact Stage4
full-CLI closure with 2,095 collected sources. After 750.8 seconds it had
completed only 202 parse entries, so the run was terminated under the repository
runaway guard. The retained trace is:

`build/native_probe/main_closure/logs/stage4-generic-close-cycle3.log`

The trace repeatedly parses the same canonical path consecutively, including:

- `src/lib/nogc_async_mut/db_atomic.spl`
- `src/lib/common/ui/theme_sync_sdn.spl`
- `src/lib/common/ui/theme_sync_diff.spl`
- `src/lib/nogc_async_mut/play/wm/mod.spl`
- `src/lib/common/ui/access_cli_grammar.spl`
- `src/lib/nogc_sync_mut/io/process_ops.spl`

This is not the former first-file `Map.keys` crash or the generic-close dedent
failure: the same run passed both and advanced through T32 and MCP sources.

## Required fix

Deduplicate the entry-closure parse queue by canonical source path before phase
2. Alias/module resolution may retain multiple logical import names, but each
physical source must be parsed once and its parsed module reused.

## Acceptance criteria

1. The Stage4 trace contains at most one `phase2:parse:file:start` for each
   canonical source path.
2. The collected-source and unique-source counts are reported separately when
   phase profiling is enabled.
3. The exact full-CLI Stage4 closure completes within the bounded bootstrap
   guard without cache deletion or seed fallback.
4. A focused regression covers two import aliases resolving to one source and
   proves one parse/module result.
