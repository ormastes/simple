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
| REQ-SMUX-CORE-005 | Actual service named layout selection, persisted canvas/rectangles, refusal, focus/window ownership and manual invalidation | `smux_service_layouts_spec.spl`, 7 scenarios |
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
in this Windows checkout. The 35 scenarios are authored, not executed.
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
current application set has 96 scenarios. Five compiler regressions are a
separate gate; they must run against a producer containing the MIR repair.

| Executable under `test/` | Authored cases | Manual under `doc/06_spec/` | Main trace |
|---|---:|---|---|
| `03_system/tools/smux_service_features_spec.spl` | 15 | `03_system/tools/smux_service_features_spec.md` | CORE-001..004 |
| `03_system/tools/smux_windows_conpty_features_spec.spl` | 3 | `03_system/tools/smux_windows_conpty_features_spec.md` | WIN-001 |
| `03_system/tools/smux_named_layouts_spec.spl` | 10 | `03_system/tools/smux_named_layouts_spec.md` | LAYOUT-001..003 |
| `03_system/tools/smux_service_layouts_spec.spl` | 7 | `03_system/tools/smux_service_layouts_spec.md` | CORE-005 |
| `03_system/tools/smux_protocol_features_spec.spl` | 57 | `03_system/tools/smux_protocol_features_spec.md` | PROTOCOL-001..004, CORE-001..004 |
| `03_system/tools/smux_windows_owner_lifecycle_spec.spl` | 4 | `03_system/tools/smux_windows_owner_lifecycle_spec.md` | WIN-002..004, LAYOUT-004 |
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

The separate `smux_windows_owner_lifecycle_spec.spl` adds four unexecuted
live-host scenarios with an authored mirrored manual. REQ-SMUX-WIN-002 covers
detached background draining, REQ-SMUX-WIN-003 separate shells/windows/request
processes, REQ-SMUX-WIN-004 authenticated external control, and
REQ-SMUX-LAYOUT-004 all five layout commands and real-shell plain composite.
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
or ConPTY resize notification proof. Root owns final review of this added lane.
