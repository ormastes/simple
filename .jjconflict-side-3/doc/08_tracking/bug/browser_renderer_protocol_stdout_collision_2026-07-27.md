# Browser renderer protocol shares ordinary stdout

Status: fixed

The sandbox renderer previously wrote SBR1 on stdout. Renderer/layout code can
also print diagnostics, so hostile or merely degenerate page input could inject
bytes ahead of a valid frame and force a protocol failure.

The 2026-07-27 bounded fix attempt routed SBR1 through child fd 3 while sending
stdout/stderr to `/dev/null`. The live sandbox transport check still failed to
observe `sandbox-ok` after three fix/verify cycles, so the unproven change was
reverted.

The replacement uses one inherited full-duplex Unix socket: the worker reads
and writes protocol messages on fd 0 while stdout and stderr go to `/dev/null`.
This needs no descriptor above stderr, so it remains compatible with the
existing `RLIMIT_NOFILE` policy.

Evidence:

- the Linux containment test enters Landlock/seccomp, writes noise to stdout
  and stderr, and receives only `sandbox-ok` through the protocol socket;
- `runtime_process.c` compiles for MinGW with `-Wall -Wextra -Werror`.

## Buffered Stop update (2026-07-29)

The broker now defers Stop when a command is partially written:
`stop_after_write` completes that frame, cancels provisional navigation/network
state, and emits one Stop. The worker drains complete messages already retained
by its bounded decoder, including Stop coalesced behind a preceding command,
before blocking for input. Pure-Simple runtime evidence remains
compiler-blocked; no bootstrap or seed result is claimed.
