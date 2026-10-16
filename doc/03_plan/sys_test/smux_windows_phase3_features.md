# SMUX Windows core-feature verification

Date: 2026-10-16. Branch: `work/smux-windows-phase3-20261016`, based on
`release_phase3`. Host: native Windows PowerShell.

## Scope and evidence

The requested existing core features are exercised through production
`os.apps.smux.api`, rather than locally reimplemented service helpers.
These requirements are acceptance criteria derived from the user's selected
session/window/split/background/multiple-screen scope, not newly selected
optional product features.

| Requirement | Production behavior | Executable evidence |
|---|---|---|
| REQ-SMUX-CORE-001 | Separate sessions, multiple windows, focus, ownership rejection | `smux_service_features_spec.spl`, 3 scenarios |
| REQ-SMUX-CORE-002 | Horizontal and vertical splits, separator geometry, minimum sizes, invalid direction rejection | same, 4 scenarios |
| REQ-SMUX-CORE-003 | Addressed-pane resize and focus; invalid size/address cannot mutate state or metrics | same, 3 scenarios |
| REQ-SMUX-CORE-004 | Multiple attachments, detach/reattach persistence, capacity refusal, client rebinding | same, 5 scenarios |
| REQ-SMUX-CORE-005 | Actual service named layout selection, persisted canvas/rectangles, refusal, focus/window ownership and manual invalidation | `smux_service_layouts_spec.spl`, 8 scenarios |
| REQ-SMUX-WIN-001 | Real ConPTY output, background execution with no clients, shell-state continuity, independent live panes | `smux_windows_conpty_features_spec.spl`, 3 scenarios |
| REQ-SMUX-LAYOUT-001 | Five named layouts, bounded nonoverlapping geometry, odd dimensions/counts, insufficient-area refusal | `smux_named_layouts_spec.spl`, 3 scenarios |
| REQ-SMUX-LAYOUT-002 | Per-window selection retained across focus, feed, zoom, resize, pane addition/removal | same, 4 scenarios |
| REQ-SMUX-LAYOUT-003 | Real model compositor honors row and tiled positions, addition refuses overflow | same, 3 scenarios |

The service, model, protocol and live-owner specs live under `test/03_system/tools/`; their manuals mirror that path
under `doc/06_spec/03_system/tools/`. No test-only service implementation is
used. Assertions in reusable setup helpers validate the actual service result.
All scenarios use `step(...)` and canonical matchers.

The live Windows suite explicitly requires `sosix_platform() == "windows"`.
It must fail on another host rather than silently execute an empty branch.
`cmd.exe /d /q` children expand output markers from environment variables;
the expanded marker is absent from submitted input, so input echo cannot
satisfy the output oracle. Capture polling is bounded to 100 attempts with
50 ms sleeps (at most five seconds sleep, plus capture and runner work).
Background progress is observed through active capture/drain calls while no
service client is attached; it does not prove unattended owner progress without
polling. The later command checks retained child-owned
state. Every successful scenario closes the child; setup resets reap children
from a preceding failed scenario.

## Current result and required execution

**TEST_BLOCKED**: no admitted general pure-Simple SSpec runtime is available
in this Windows checkout. All scenarios below are authored, not executed.
Manual mirrors are authored review copies; SPipe generation, zero-stub
validation, `sspec-maintain` scan, and UI evidence audit remain pending.
No green result, coverage percentage, screenshot, or captured transcript is
claimed.

Once an admitted general runtime exists, run each command once, recording
the exact runner identity, exit code, case counts and artifact paths:

```text
<admitted-runtime> test test/03_system/tools/smux_service_features_spec.spl --native
<admitted-runtime> test test/03_system/tools/smux_windows_conpty_features_spec.spl --native
<admitted-runtime> test test/03_system/tools/smux_named_layouts_spec.spl --native
<admitted-runtime> test test/03_system/tools/smux_service_layouts_spec.spl --native
<admitted-runtime> spipe-docgen test/03_system/tools/smux_service_features_spec.spl --output doc/06_spec --no-index
<admitted-runtime> spipe-docgen test/03_system/tools/smux_windows_conpty_features_spec.spl --output doc/06_spec --no-index
<admitted-runtime> spipe-docgen test/03_system/tools/smux_named_layouts_spec.spl --output doc/06_spec --no-index
<admitted-runtime> spipe-docgen test/03_system/tools/smux_service_layouts_spec.spl --output doc/06_spec --no-index
<admitted-runtime> sspec-maintain scan test/03_system/tools/smux_service_features_spec.spl
<admitted-runtime> sspec-maintain scan test/03_system/tools/smux_windows_conpty_features_spec.spl
<admitted-runtime> sspec-maintain scan test/03_system/tools/smux_named_layouts_spec.spl
<admitted-runtime> sspec-maintain scan test/03_system/tools/smux_service_layouts_spec.spl
<admitted-runtime> test test/03_system/app/testing/feature/ui_sspec_evidence_audit_spec.spl --native
```

Compiled mode must execute actual examples; interpreter loading alone cannot
satisfy these acceptance criteria. Preserve executable inventory and run counts,
including failed, blocked and unexecuted cases, rather than trusting source
discovery counts as proof of execution.

A Phase 2 or Phase 3 diagnostic compiler build can establish source parsing,
lowering or linkage only to the extent its actual result demonstrates. It is
not an admitted general SSpec runner, does not execute these examples merely
by compiling an app, and cannot establish runtime or release acceptance.

## Open parity gaps

The service scenarios prove attachment records, not multiple independent
screen processes connected to a persistent daemon. The live scenarios prove
one-process service lifetime, not terminal disconnect/restart persistence.
Service named-layout selection now persists complete canvas geometry and exposes
actual pane rectangles; its direct-owner suite remains unexecuted. Successful
directional split, close or arbitrary pane resize explicitly invalidates the
named plan to manual mode. The separate pure-model suite exercises named layouts
and two-dimensional text compositing. Live child size notifications and actual
host rendering remain unproven. Copy mode, configurable
key tables, mouse interaction, tmux config parsing, control mode, independent
client rendering, and full tmux parity require their own implementation and
live evidence. The legacy `smux_system_spec.spl` remains contract/test-double
evidence and must not substitute for these production-service checks.

## Ownership and review

SSpec lane owns the four new specs, manual mirrors, pure model/geometry and
service/contract named-layout integration and this plan. Root owns
production fixes; build lane owns compiler provenance and Windows build
results. Astra reviews broad parity and source behavior. No lower-model
sidecar was used in this lane (N/A). Root is merge owner and final reviewer.

## Consolidated source and pending execution inventory

All counts below describe authored scenarios, never executed passes. The
inventory records authored case counts per file. Later unit/native fixture
additions are separate gates; none is an executed pass. Compiler regressions
must run against a producer containing the MIR repair.

| Executable under `test/` | Authored cases | Manual under `doc/06_spec/` | Main trace |
|---|---:|---|---|
| `03_system/tools/smux_service_features_spec.spl` | 15 | `03_system/tools/smux_service_features_spec.md` | CORE-001..004 |
| `03_system/tools/smux_windows_conpty_features_spec.spl` | 3 | `03_system/tools/smux_windows_conpty_features_spec.md` | WIN-001 |
| `03_system/tools/smux_named_layouts_spec.spl` | 10 | `03_system/tools/smux_named_layouts_spec.md` | LAYOUT-001..003 |
| `03_system/tools/smux_service_layouts_spec.spl` | 8 | `03_system/tools/smux_service_layouts_spec.md` | CORE-005 |
| `03_system/tools/smux_protocol_features_spec.spl` | 57 | `03_system/tools/smux_protocol_features_spec.md` | PROTOCOL-001..004, CORE-001..004 |
| `03_system/tools/smux_windows_owner_lifecycle_spec.spl` | 7 | `03_system/tools/smux_windows_owner_lifecycle_spec.md` | WIN-002..007, LAYOUT-004 |
| `03_system/tools/smux_scrollback_spec.spl` | 15 | `03_system/tools/smux_scrollback_spec.md` | HISTORY-001..005 |
| `01_unit/compiler/driver/windows_native_provider_composition_spec.spl` | 6 | `01_unit/compiler/driver/windows_native_provider_composition_spec.md` | WINDOWS-NATIVE-PROVIDER-SELECTION |
| `01_unit/lib/io/windows_pty_codec_spec.spl` | 8 | `01_unit/lib/io/windows_pty_codec_spec.md` | Native coordinate/UTF-8 validation |
| `01_unit/os/apps/smux/interactive_frame_spec.spl` | 6 | `01_unit/os/apps/smux/interactive_frame_spec.md` | INTERACTIVE-002,004 |
| `03_system/tools/smux_interactive_protocol_spec.spl` | 5 | `03_system/tools/smux_interactive_protocol_spec.md` | INTERACTIVE-002..004 |
| `03_system/tools/smux_interactive_windows_input_spec.spl` | 1 | `03_system/tools/smux_interactive_windows_input_spec.md` | INTERACTIVE-002 |
| `03_system/tools/smux_client_input_spec.spl` | 15 | `03_system/tools/smux_client_input_spec.md` | INTERACTIVE-001 |
| `01_unit/os/apps/smux/client_view_spec.spl` | 10 | `01_unit/os/apps/smux/client_view_spec.md` | INTERACTIVE-002..005 |
| `01_unit/compiler/mir/pty_spawn_transfer_boundary_spec.spl` | 5 | `01_unit/compiler/mir/pty_spawn_transfer_boundary_spec.md` | WINDOWS-PTY-SPAWN-OWNER |

All shortened trace labels have the `REQ-SMUX-` prefix. Actual source includes
explicit full requirement IDs. The compiler reproducer is
`test/fixtures/compiler_entrypoint/pty_spawn_transfer_owner/main.spl`.
Requirements/NFR, architecture and detail design use the matching
`smux_windows_phase3_features` slug in their respective documentation trees.

Execute the protocol, service-layout, named-layout and live-owner additions
with the admitted runtime's `test <path> --native`, preserving exact executed
case counts and fixture identity. Generate each mirrored manual and require
zero stubs, then run `sspec-maintain scan <path>` once. These commands have not
been run. The compiler change additionally requires the core/compiler/lib and
MCP/LSP smoke matrix from AGENTS.md, which is blocked by unavailable matching
qualified producers. The unadmitted old compiler cannot validate its repair.

## Independent owner live-host addition

The separate `smux_windows_owner_lifecycle_spec.spl` adds seven unexecuted
live-host scenarios with an authored mirrored manual. REQ-SMUX-WIN-002 covers
detached background draining, REQ-SMUX-WIN-003 separate shells/windows/request
processes, REQ-SMUX-WIN-004 authenticated external control, and
REQ-SMUX-LAYOUT-004 all five layout commands and real-shell plain composite.
REQ-SMUX-WIN-005 resizes a live single-pane session to 120x30 through the remote
layout command, then requires a real PowerShell child to compute exactly those
Console.WindowWidth/Height values. The expected result is absent from command
input. This is application-to-provider resize evidence only after execution.
REQ-SMUX-WIN-006 starts a real child that sleeps without reading stdin, offers
bounded input until typed capacity refusal and queued/pending delivery, then
requires another session's actual expanded output in less than 5000 monotonic
milliseconds while the blocked pane remains pending. Its external watchdog
receipt (at most 180 seconds per native case) is a mandatory execution gate.
REQ-SMUX-WIN-007 generates 160 computed child lines, waits on the actual screen
for completion, and requires the production history command to return older
lines absent from that visible screen. No capture substitute or test buffer is
accepted as history evidence. Both scenarios remain authored and unexecuted.
Every command runs a separate compiled client. `SMUX_TEST_BINARY` must point to
the real prebuilt `.exe`; missing binary/host/TCP/ConPTY fails without skips.

The detached-drain oracle is a child-written file after more than 1 MiB output.
A release-file handshake prevents that burst from starting until after detach;
the child's PowerShell wait has a 30-second bound.
The harness issues no requests or captures while awaiting that file (300 x
50 ms maximum sleep). This closes the weakness in the older actively polled
in-process scenario once the new scenario actually passes. The wait polls exact
child-written contents, so file creation before writing cannot end it early.
Expanded markers
distinguish child execution from terminal input echo. Scenario assertions run
after finite authenticated shutdown/fallback termination and reap.

Execution remains TEST_BLOCKED pending an admitted runner and actual compiled
application. The additional commands are:

```text
SMUX_TEST_BINARY=<actual-phase2-or-phase3-smux.exe> <admitted-runtime> test test/03_system/tools/smux_windows_owner_lifecycle_spec.spl --native-backend=llvm
<admitted-runtime> spipe-docgen test/03_system/tools/smux_windows_owner_lifecycle_spec.spl --output doc/06_spec --no-index
<admitted-runtime> sspec-maintain scan test/03_system/tools/smux_windows_owner_lifecycle_spec.spl
```

Use PowerShell environment assignment on Windows; the first line above records
the required fixture binding, not shell-specific assignment syntax. Retain exact
compiler/runner/application hashes and runtime identities. This lane provides
no green result, generated manual receipt, interactive screen renderer evidence,
or executed ConPTY resize notification proof. Root owns final review of this added lane.

The older `smux_windows_conpty_features_spec.spl` close operations now use the
shared bounded `windows_close_shell` helper: retry pending provider cleanup up
to 100 calls with 10 ms sleeps, then assert true once. False remains a pending
cleanup result and cannot satisfy the closure oracle. Its manual describes the
same bounded policy. These changed scenarios have not been executed.

## Actual interactive terminal fixture addition

`test/fixtures/compiler_entrypoint/windows_smux_interactive/main.spl` launches
the real compiled owner and two compiled `--attach` clients under three leased
native ConPTY terminals. Client keyboard input performs split, layout cycling,
new/next-window and detach; authenticated RPC only creates sessions and observes
state. Expanded child markers prove input/output delivery and cross-session
render-stream isolation. After alpha detaches, beta must still execute commands
and the owner must retain both sessions. Both clients and owner must report real
exit code zero through the retained PTY provider handle before leases close.
All acquired leases reach bounded cleanup before a final PASS can be printed.

The manual/pending report is
`doc/09_report/smux_windows_interactive_fixture_2026-10-16.md`. Both Phase 2 and
Phase 3 must build the application and fixture, select actual Windows TCP,
ConPTY and console overlays, then run under an external <=180s process-tree/Job
watchdog with exact producer/artifact hashes and cleanup receipts. No build,
native execution or watchdog outcome is claimed; the seven owner SSpec cases
remain unchanged by this fixture addition.

## Bounded input ownership and portable compatibility addition

| Executable under `test/` | Authored cases | Manual under `doc/06_spec/` | Trace |
|---|---:|---|---|
| `01_unit/os/apps/smux/input_queue_spec.spl` | 12 | `01_unit/os/apps/smux/input_queue_spec.md` | REQ-SMUX-INPUT-001 |
| `01_unit/lib/sys/pty_input_codec_spec.spl` | 8 | `01_unit/lib/sys/pty_input_codec_spec.md` | REQ-SMUX-INPUT-002 |

INPUT-001 covers the 65536-byte retained storage limit, atomic overflow refusal,
4096-byte prefixes, partial UTF-8 byte offsets, no replay, sticky deferred errors
and production PaneRecord ownership transitions. The tests call production pure
queue helpers; supplied acceptance counts and error reasons do not claim native
backpressure or process execution.

INPUT-002 covers the portable text-only adapter's complete UTF-8 prefixes,
4095-ASCII-plus-emoji boundary, two/three/four-byte cuts, scalar validity and byte
roundtrip. The selected native byte provider must separately prove arbitrary
byte-prefix delivery; portable codec tests cannot establish that provider gate.

Both specs and authored manuals remain **TEST_BLOCKED** and unexecuted.
After runner admission, execute each spec once, generate its mirrored manual
with zero stubs and run `sspec-maintain scan` using the actual qualified runtime.
Record exact runtime/producer hashes, executed counts, exit status and artifacts.

Source review confirms that query replies enter the same production pane queue;
overflow latches a typed input error and clears the VT reply accumulator instead
of retaining an unbounded secondary queue across calls. Each drain/API flush
offers at most one 4096-byte provider write. A server outer turn can invoke both
polling and command dispatch, so this is a per-call bound, not one write per outer
turn. Polling visits the service's finite pane table and request dispatch uses
the finite client table and request/reply limits. These source bounds do not
prove real provider fairness or latency; the portable legacy text provider is
still synchronous. Live native pressure/deferred-error evidence remains required.

## Interactive continuation gates

The same hosted entry now has an authored `--attach` path. Additional pending
specs include `smux_client_copy_input_spec.spl` (incremental copy keys),
`smux_interactive_client_sizes_spec.spl` (actual attachment metadata and an
interleaved split/frame regression), and the Win64 console codec spec. These
pure/service scenarios do not prove two rendered clients.

Native compiler-entrypoint fixtures now cover Windows TCP lease reuse, ConPTY
input/resize/cleanup, console input/mode restoration/bottom-right rendering,
ordered provider selection, and two actual hosted interactive clients. Run
each relevant fixture under both matching Phase 2 and Phase 3 producers, with
separate caches and exact hashes, and retain an outer watchdog receipt. The
two-client workflow is detailed in
`doc/09_report/smux_windows_interactive_fixture_2026-10-16.md`.

General runner admission remains a separate prerequisite for actual SSpec,
SPipe docgen and maintenance, core/compiler/lib checks, and MCP/LSP smoke.
Native fixture PASS alone cannot satisfy those gates. Direct user32 clipboard
imports additionally require actual selected-link evidence; default library
lists in source do not certify that the product link used them.

The current pending matrix also retains unexpected-client crash cleanup,
same-session clients of different live console sizes, automatic background
owner launch/discovery, mouse/key-table/config/control compatibility and
realistic startup/request/RSS measurements. No source-only feature addition
removes these requirements or marks full tmux parity complete.
