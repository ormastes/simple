# MCP bridge owned-child lifecycle repair

Canonical bug: lsp_mcp_server_process_leak_2026-07-05, P2 open, reproducer NONE.
Base db7b22dabb591d29dd68a55083b421052d51a00c. Historical 48 native server
processes have no recorded spawner identity; that attribution remains unresolved.
Current Simple LSP stdio loop exits on EOF, and diagnostics already use bounded
process cleanup. No singleton, idle timeout or unrelated process sweep is added.

## Concrete reproduced owner

bin/mcp_stdio_bridge.js spawns the transport child. Before repair, child startup
errors only logged; no exit listener ran after ENOENT, leaving the bridge on open
stdin. Client EOF merely closed child stdin, leaving an EOF-ignoring child alive.
These are actual reproduced bridge failures, not proof of the historical spawner.

Test-first commit e999fb3e27b contains real Node subprocess tests and a synthetic
JSONL fixture. On Node v24.19.0 Windows, first run: 4 tests, 2 passed, 2 failed,
no skips/cancellations, duration15148.0124ms. Failures were spawn-failure bridge
hang and EOF-ignoring child/bridge survival. Fixture cleanup finished in finally.
After the narrow owner patch: 4 passed, 0 failed, no skips/cancellations,
duration6838.1222ms. A subsequent harness change adds explicit absolute temp-path
validation before recursive cleanup. Its one justified TAP-format verification
passed4/4 with no skips/cancellations in6137.116ms. No unchanged green checks were
repeated. One production repair cycle per cause; no further run is needed.

## Contract and implementation

REQ-MCP-BRIDGE-LIFECYCLE-001: ordinary client EOF closes child stdin and waits for
child exit/stdio close. REQ-002: startup failure yields a nonzero bridge exit even
if client stdin stays open. REQ-003: EOF shutdown waits1s, sends SIGTERM to only
the owned direct child, then after another1s sends SIGKILL if no exit event.
REQ-004: three independent cooperative sessions leave all their children gone.
The executable spec spells the full REQ-MCP-BRIDGE-LIFECYCLE-NNN identities.

The bridge handles close, which also follows spawn failure; exit alone does not
cover that case. It waits for child pipes before finishing stdout, cancels timers
on child exit, and prevents writes after shutdown. SIGINT/SIGTERM route through
the same owned-child cleanup on platforms that deliver them to Node. Windows
forced process termination cannot run Node signal handlers; no signal-path runtime
claim is made. Descendant process-tree cleanup is not claimed by this direct-child
bridge contract. The child command is launched without a shell.

Node primary API reference: https://nodejs.org/api/child_process.html
The close event follows exit or failed-spawn error; killed indicates signal delivery,
not observed process termination. Implementation uses exit observation, not killed.

## Ownership and evidence limits

Each test has a private mkdtemp directory and stop-file watched only by its fixture.
Finally asks that fixture to exit through its private file, waits for its PID to
vanish, then kills only the owned bridge ChildProcess handle if still active.
No name-based kill, process enumeration, unrelated PID signal, external account,
bootstrap, or native Simple process is involved. Temp logs are disposable fixture
logs; committed SDN records tool-observed counts/durations, not a fabricated raw log.

The modern SSpec wrapper is AUTHORED_UNRUN. Native Simple EOF/initialize lifecycle,
self-hosted runner, docgen zero-stub admission, POSIX signal branch, and branch
coverage remain unverified. Do not close the original unattributed orphan bug solely
on this bridge repair. Final exact source review: Astra; landing owner: root.
