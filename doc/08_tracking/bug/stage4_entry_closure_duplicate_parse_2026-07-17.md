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

## 2026-07-17 continuation

Phase 2 now builds a unique physical-source parse plan using lexical path
normalization, parses each physical file once, caches the resulting `Module`
in explicitly reassigned arrays, and registers that same result under every
logical alias. Phase profiling now reports `collected` and `unique` source
counts separately. The focused two-alias plan regression passed under the
bootstrap seed before the final dictionary-to-array reliability hardening; the
final source awaits executable re-verification in the next bounded cycle.

Executable Stage4 acceptance remains open because the retained Stage3 spends
over seven minutes in phase 1 before the new phase-2 code can run. A refreshed
24 MiB pure-Simple Stage3 was built successfully (714 compiled, zero failed,
99.7 seconds) using an isolated source-correct runtime overlay. Replacing the
phase-1 membership arrays with local `Dict<text, bool>` values was rejected:
the refreshed Stage3 reproduced the known compiled-dictionary mutation defect,
reached 12.7 GiB RSS in 85 seconds, and never left source loading. That unsafe
change was removed.

The next bounded continuation must implement a reliable array-backed
open-addressed text set (exact string comparison after hash probing) for the
phase-1 loaded-module, queued-import, and scanned-path sets, rebuild Stage3,
then verify the phase-2 unique count and one-parse-per-path trace. No further
Stage4 retry is permitted in the current continuation because the three-cycle
cap was reached.

## 2026-07-17 macOS arena continuation

The array-backed closure sets and unique physical-source plan now run in a
fresh 24 MiB pure-Simple Stage3. Stage4 phase 1 completed in 26.643 seconds and
reported 2,020 collected sources and 1,246 unique physical sources. Phase 2
advanced through roughly 174 unique files without the former duplicate parse
or compiled-`Map` crash. This satisfies the collection/counting portion of the
fix; full executable acceptance remains open.

The bounded retries then isolated the remaining growth to flat AST reset and
bootstrap environment mirroring. Reusing the declaration/expression/statement
arrays reduced RSS at the like-for-like 157-file point from about 9.3 GiB to
7.9 GiB (about 15%). Source now also disables per-node expression/statement
environment mirrors while the native arena is authoritative, and native
readers bypass stale keys from prior modules. The aggregate AST modules compile
successfully through the bootstrap gate. A fresh Stage4 executable run is
deferred to the next continuation because this continuation reached the
mandatory three-cycle cap.
