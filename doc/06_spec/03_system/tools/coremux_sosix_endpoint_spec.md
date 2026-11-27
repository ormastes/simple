# coremux_sosix_endpoint_spec

STATUS: NOT_RUN. 3 authored cases,0executed,0runtime passes.
Manual authored from current SSpec source; native docgen has not run.

Source: `test/03_system/tools/coremux_sosix_endpoint_spec.spl`.

Actual new framed server, real child processes/terminals, split/background reconnect/input/authentication and cleanup. Requires separately admitted product/child and private owned endpoint fixtures; no fake server substitutes.

## Authored cases

1. runs real background children across split disconnect reconnect and literal input
2. rejects wrong authentication on an independently proven live endpoint
3. reports a real reserved unlistening endpoint without claiming fallback success

## Visible steps

- Use the admitted framed server and real terminal echo child
- Clean only recorded owned sessions and child processes
- Prove the actual server then refuse a wrong private token
- Observe unavailable transport before mutation submission

## Admission and evidence

Use only an admitted current Phase3 compiler and matching runtime/full modern
SSpec runner with semantic --library-mode nogc-sync-mut and generic library roots.
Do not select a family by --source directory, use a seed, rebuild Phase2 for this
suite, or accept missing framework imports as a passing run. No exact executable
or invocation is admitted by this source checkpoint.

Retain producer/source/runtime hashes, actual argv, stdout/stderr, exit status,
case totals with failures/blocked/unrun, resource peaks and cleanup receipts.
Auth tokens and pane content are excluded from diagnostic errors and public reports.
Private expected fixture text is inspected only by assertions/owned artifacts.
All current cases remain NOT_RUN; source checks are not native test evidence.


## Required real fixture

The coordinator provisions an exclusive namespace on the NEW authenticated framed
Smux listener, independent from the legacy line listener. It exports through the
normal application environment facade:

- SIMPLE_TEST_COREMUX_PORT: configured listener port.
- SIMPLE_TEST_COREMUX_AUTH: private operator-owned credential, never public logs.
- SIMPLE_TEST_COREMUX_NAMESPACE: exclusively owned initially empty namespace.
- SIMPLE_TEST_COREMUX_CHILD_EXE: admitted native build of test/fixtures/coremux/wire_echo_child.spl.
- SIMPLE_TEST_COREMUX_UNLISTENING_PORT: a coordinator-owned reserved/bound socket
  that deliberately does not listen, distinct from the real server port.

Missing fixture prerequisites fail with TEST_BLOCKED evidence; an absent or legacy
line server cannot pass the positive case. The negative unavailable-endpoint row
is not feature qualification. Run this file serially in that exclusive namespace.
The coordinator must supply a finite independent process guard, own endpoint/server
cleanup, and verify zero leaked children/leases/resources afterward, including
failure paths. The spec attempts known owned session cleanup before assertions;
uncertain lease/creation evidence remains an error and requires owner reconciliation.
It never turns unknown cleanup into absence/success or kills unrelated processes.

The actual child prints COREMUX_CHILD_READY and echoes terminal line input as
COREMUX_ECHO:<line>. The spec uses std.sosix.process.sosix_process_exists for
externally owned PID presence. It does not use a local spawn registry or a process
HANDLE API as an arbitrary-PID oracle. Presence is provider-dependent evidence;
PID reuse and permissions can affect observations. It is not process-incarnation
identity or complete resource cleanup proof. The external guard must bind actual
server/child ownership and incarnation and audit resources independently.

The split must retain the original pane/PID and introduce a distinct pane with a
distinct present PID. The second pane must independently capture readiness, accept
its own COREMUX_SPLIT_PING literal plus Enter, and capture the corresponding echo.
Both identities/PIDs must remain present in the reconnect observation. The first
pane separately echoes COREMUX_PING after reconnect. Geometry, receipt correlation
and the new reconnect lease token are also checked.

All successful disconnect paths, including the second client, final cleanup lease
and authentication-case releases, require cleanup.pending=false. Pending cleanup
remains failure even when PIDs are absent. PID absence is only one observation:
checked owner receipts plus the mandatory external guard's identity/resource audit
are required before reporting full cleanup. Unknown effects stay unresolved errors.
This is a focused system slice, not the complete Caret/IDE/Tmux suite or N2 soak.

Correction cycle3 changes only this endpoint spec/manual and the separate design
note. Production codec/client v2 pins remain unchanged. Three endpoint cases and
all28 checkpoint cases remain NOT_RUN; zero runtime passes.
