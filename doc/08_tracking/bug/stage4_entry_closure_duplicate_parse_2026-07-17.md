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

## 2026-07-17 macOS grammar-hardening continuation

A fresh pure-Simple Stage3 (24 MiB, 707 compiled, zero failed) verified the
native-arena source and drove three bounded Stage4 cycles. Phase 1 improved
from 21.974 seconds to 18.271 seconds while retaining the 2,020 collected /
1,246 unique physical-source plan. The cycles exposed and fixed two real
source grammar incompatibilities in the browser lane:

- parenthesized the multi-line static-frame predicate in
  `src/app/ui.browser/backend.spl`;
- replaced multi-line `=>` match arms with canonical colon arms in
  `src/app/ui.browser/event_bridge.spl`.

Both files pass focused bootstrap compilation. The third cycle advanced to
`src/lib/nogc_async_mut/io/tcp.spl` at 127.075 seconds and exposed missing
comma-list support for established `class X with A, B, C` syntax. The Stage4
frontend now consumes all comma-separated mixin identifiers, and the Simple
parser probe parses the real async TCP module through `PROBE_DONE`.

No fourth Stage4 run was started because the mandatory three-cycle cap was
reached. Full executable acceptance remains open; the next bounded
continuation should rebuild Stage3 with the comma-list parser fix and resume
the exact Stage4 command without deleting caches.

## 2026-07-17 macOS generic-and-web continuation

Three bounded Stage4 cycles retained the 2,020 collected / 1,246 unique source
plan and the roughly 10.3 GiB RSS plateau. The first reached
`src/lib/common/sdn/value.spl` at 196.622 seconds and exposed that generic type
branches returned before consuming an optional `?` suffix. `Option`, `Result`,
`Dict`, named-generic, and unknown-generic returns now all pass through
`parser_absorb_optional_suffix`; a focused `Dict<text, i64>?` native probe
completed successfully.

The second cycle passed `SdnValue` and reached
`src/app/ui.render/html_widgets.spl` at 187.263 seconds. The Stage4 parser
accepted `=>` only for same-line expressions, while the established web/UI
source uses `=>` followed by an indented statement block. Fat-arrow arms now
route a following newline through `parse_block`; the exact multiline match
form compiled and ran as a focused native probe (`ok`, exit 0).

The third and final permitted cycle passed both earlier failures, including
the HTML renderer, and reached
`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` at 213.094 seconds. It
rejected an uninitialized `Engine2D` local, as required by the declared-type
initialization gate. The offscreen selection now uses an explicitly initialized
`Engine2D?`, assigns `Some(created)` on every backend path, and unwraps only
after selection. No fourth full closure run was started. Full executable
acceptance remains open at this later Engine2D boundary.

## 2026-07-17 macOS public-trait and module-order continuation

The first bounded cycle used the pushed Engine2D fix, retained a 2,021
collected / 1,247 unique source plan, passed the prior Engine2D boundary, and
reached `src/compiler/70.backend/backend/codegen_types.spl` at 327.422 seconds.
It exposed that visibility dispatch omitted the established `pub trait` form.
The parser now routes public traits through `parse_struct_or_trait_decl`, and
a focused native `pub trait` probe compiled and ran (`ready`).

After the latest remote compiler changes were incorporated into Stage3, cycles
two and three both SIGBUSed immediately after phase 2 began. macOS crash reports
identified `Map.keys` called from `desugar_async.desugar_module`; the receiver
was the tagged runtime `Dict` created by the required `{}` initializer, not a
`Map` struct. Rewriting `Map.keys` traversal did not change the fault and was
reverted, proving its body was not the cause.

The frontend `Module` now carries explicit `function_order` and `actor_order`
arrays populated during flat-AST assembly. Async desugaring consumes those
arrays and records generated helper names as they are created, removing its
three `.keys()` snapshots without reintroducing the interpreter-corrupting
`Map.new()` spelling. All `Module` construction paths carry the new fields. A
fresh Stage3 rebuilt incrementally (8 compiled, 700 cached, zero failed), then
compiled and ran a new native module (`ready`). No fourth full Stage4 cycle was
started; executable acceptance remains open for the next bounded continuation.

## 2026-07-17 post-sync current-source continuation

After rebasing and pushing `54ad67393a16`, the Rust bootstrap seed rebuilt the
pure-Simple bootstrap compiler with the preserved cache: 7 objects compiled,
701 reused, 0 failed, producing the 24 MiB `simple-current` artifact.

One exact Stage4 `src/app/cli/main.spl` cycle used that compiler, the canonical
four source roots, `core-c-bootstrap`, Cranelift, entry closure, low-memory, and
the isolated Stage4 cache. It passed the prior immediate `Map.keys` SIGBUS but
remained pre-object: after 8m24s it was still at 100% CPU, RSS had climbed to
9.0 GiB, and the log, cache, and output remained empty. The process was stopped
at the host-protection boundary. Repeating the identical full build would be a
runaway-guard violation; the next compiler work must expose bounded phase
progress or reduce the pre-object resident set before another full cycle.

The same current bootstrap compiler successfully built the canonical MCP and
LSP entries in isolated shards (53 and 9 compiled units respectively). Direct
native framed initialize, tools/list, and tools/call requests all preserved IDs
with zero stderr/protocol/tool errors; the correlated `lsp_symbols` response no
longer contains `Missing tool name`. This proves the MCP/LSP source corrections
independently of the still-missing monolithic CLI.

A focused Metal parity archive also compiled from current source (1 compiled,
105 cached), showing that the added GPU-only clip path closes at Simple compile
time. Native execution is separately blocked by the missing canonical macOS
`simple-core` runtime archive: the supported core-C lane lacks Metal symbols,
while the removed legacy hosted lane is no longer selectable. This runtime
packaging issue does not justify another monolithic Stage4 attempt.
