# Native HIR failures lost from bounded compiler logs

Status: source repair tested; integration into the next native packet remains
unqualified. Active packets and their evidence are unchanged.

## Observed failure

`p4-type-budget-efc724-newp2-retained-j40` produced2593 canonical HIR terminal
receipts:2584 PASS and9 FAILED/UNCACHED. Repeated/local progress counters that
said2593 succeeded are not authoritative. The failed source identities are:

- `src/app/mcp_t32/action_tools.spl`
- `src/app/mcp_t32/ctypes_bridge.spl`
- `src/app/mcp_t32/gap_tools.spl`
- `src/app/mcp_t32/headless_tools.spl`
- `src/app/mcp_t32/session_tools.spl`
- `src/app/mcp_t32/window_tools.spl`
- `src/app/editor/gui_shell.spl`
- `src/lib/editor/70.backend/gui_sdl_bridge.spl`
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl`

These form source-area groups of6,2,1, not established root-cause groups.
The full pinned receipts, per-source digests and log metadata are retained in
`p4-efc-nine-hir-failure-groups.json` in the Windows restart evidence directory.
No MIR or executable link was reached by this failed HIR aggregate.

The pipe observer saw56,249,870 bytes, retained4,194,304, and dropped52,055,566.
The retained head/tail contains no `[hir-fatal]`, `[hir-owner-fatal]` or
`[hir-fatal-count]` messages. Native temporary logs were absent after completion.
Builtin re-export warnings must not be promoted to the missing fatal causes.
An unchanged compile is not repeated merely to recover these lost messages.

## Repair

The existing bounded-error-summary helper now also exposes an incremental
`DiagnosticStreamSummary`. The reusable pipe adapter feeds every observed byte
to it before bounded head/tail truncation. It writes `diagnostics.json` with
the full stream digest, byte offsets, bounded event prefixes and explicit
observed/retained/dropped/truncated counts. Concatenated compiler phase markers
and markers split across pipe chunks are handled without buffering entire lines.
Default retention is64 excerpts of1024 bytes. Event count is a marker count,
not a distinct-error or failed-module count.

The adapter pins the helper before loading it, preserves the native exit code,
keeps draining after observer failure, and reports incomplete observation rather
than inventing a compiler result. Canonical outer process containment and RSS
receipts remain the only closure authority. Head/tail and live-tail behavior
are unchanged. This utility is diagnostic-only, not a production default switch.

The unfrozen `p3-any-only-diagnostic-next-producer-j40` caller now supplies the
pinned helper; no running collector, source snapshot or cache was changed.

## Verification

Seven focused Python tests PASS in15.746 seconds: fatal events in the middle
of oversized output; every chunk split; unterminated events; count/truncation
limits;64 MiB single-event peak allocation below2 MiB; warning/phase exclusion;
tampered-module nonexecution; and real child exit7 with middle fatal retained
only in the summary. The last scenario uses a test double for the unchanged
logger/observer APIs and a real child process. These tests do not qualify a
Simple compiler build or repair the nine underlying HIR failures.

An eighth focused test PASS in0.330 seconds proves sparse flushed output becomes
visible in the unbuffered retained log and observer before child EOF, with no
per-byte callback loop. The live adapter uses `read1(65536)` and a bounded
eight-chunk queue. Older P2 drain wrappers using `read(65536)` and exit-only
publication must adopt this reviewed adapter in a new packet; active frozen
wrappers are not edited. A source pin and root-reviewed caller change remain
required for that P2 integration.

The pending P3 runner consumes `diagnostic_evidence()` into each compile result:
summary path/SHA, marker counts, explicit drops/truncation and at most four
512-character excerpts. The reader verifies the summary against the stream
receipt and digest; a ninth focused test PASS in0.023 seconds checks consumption,
truncation visibility and tampering rejection. Thus failure triage receives the
summary instead of depending on an otherwise unused sidecar JSON file.
