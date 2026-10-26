# Single SPL object startup: measured baseline and remaining gate

Status: target unverified; diagnostic source change only. No object compilation
below 100 ms, memory improvement, semantic PASS, or release qualification is
claimed here.

## Measured executable startup

On the active Windows host, launched the existing producer directly with
`System.Diagnostics.ProcessStartInfo` (`UseShellExecute=false`, no shell),
redirected/drained both streams, and waited for process exit. A Stopwatch covered
process creation through exit. Three sequential `--help` invocations yielded:

| Sample | Wall ms | Exit | stdout characters | stderr characters |
|---|---:|---:|---:|---:|
| 1 | 87.7280 | 0 | 348 | 0 |
| 2 | 72.6839 | 0 | 348 | 0 |
| 3 | 71.9637 | 0 | 348 | 0 |

Median: 72.6839 ms; nearest-rank p95 for this small diagnostic sample: 87.7280 ms.
This is executable startup/help, **not compilation**, a cold/warm cohort, or a
before/after comparison. Other bootstrap processes were active. PeakWorkingSet
was unavailable after these short processes exited; no RSS claim is made.

Producer:
`C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004/qualification-focused-c4-newp2-hello40-draft/producer/simple.exe`.
Supplied producer identity:
`177808075f37891aed267fde59f8a87c5ad3d3292829c10f50857fecd43ed6bb`.

Existing independent object receipt
`phase3-focused-c4-vertical1170-p40t1-budget3/artifact/module-0657/result.json`
reports 136.3646776 seconds and 3,179,960 KiB peak RSS for
`src/compiler/80.driver/cache/cache_text_join.spl`, with compile exit zero and
COFF output. Its explicit status is `OBJECT_EMITTED_UNQUALIFIED`:
any-escape, enum-contract, typecheck-warning and safety-warning passes are UNRUN.
It is not a prepared-header, entry-only measurement.

## Diagnostic change

Existing `SIMPLE_NATIVE_BUILD_WORKER_SPAWN_TRACE=1` now includes monotonic
nanosecond start/finish receipts for workaround refresh, producer/policy setup,
source inventory, warm receipt preparation, parse shards, HIR shards, worker
process and warm receipt promotion. Failed/backwards clocks report unavailable,
never zero. An unmatched start identifies a phase that returned early or stalled;
it is not a successful timing row. Disabled helpers return before clock calls or
receipt formatting. No global profile state or retained compiler context exists.

`git diff --check` passed for the edited tracked file. Seven executable unit
cases were authored, but remain UNRUN: the available producer is bootstrap-only
and there is no qualified general test runtime. Optimizer-app execution, compiler,
library and MCP checks and dynamic no-allocation proof remain UNRUN as well.

## Safe path to the actual performance gate

An additional performance change replaces publication-receipt recognition's
whole-log CRLF copy and split-line arrays with a forward line cursor. Each byte
is searched once for line boundaries and compared at most once for equal-length
candidate lines: O(log bytes) time and constant scanner auxiliary storage. It
does not copy the captured log. Exact LF/CRLF, bare CR, Unicode, blank/final-line
and multiline-needle rejection semantics remain specified by a legacy oracle.
Nine focused scanner examples and two wrapper examples were added (UNRUN).
An independently executed PowerShell UTF-8 byte model matched normalization and
split-line semantics for 4,096 boundary combinations with zero mismatches; this
is host-model evidence, **not execution of the Simple implementation**.
Large-log before/after wall time and peak RSS still require a qualified runtime;
there is no measured speedup claim for this patch.

The normal coordinator launches another compiler process. Removing that launch
must preserve environment-policy handoff, SCV admission, strict stub rejection,
artifact publication evidence, timeout/tree cleanup and failure diagnostics.
The existing positional direct route does not preserve every coordinator flag
or admission; substituting it for explicit `--entry` is not an admitted fix.
Importing the heavy worker into the lightweight source-run coordinator also
regresses wrapper startup.

An inline executor needs a compiler-owned structured completion receipt with
actual strict-stub status, output publication and watchdog/cancellation proof,
plus a compiled-only dispatch seam. A scalar exit code and fabricated empty
stdout cannot replace the current captured-output strict gate. No such bypass
is enabled by this change. Header admission also still needs real CLI/loader
wiring; merely generating typed signatures does not eliminate imported bodies.

Acceptance remains actual invocation-to-fresh-object wall time below 100 ms with
prepared valid headers, no object cache hit, no imported body compilation or
background compilation. Report header preparation, process startup, compiler
phases and link/run separately. Require semantic output 42, symbol/type/linkage
checks, stale source/header/config/capture rejection, honest generic fallback,
and concurrency/lifetime/memory evidence before adoption.
