# Windows smux shared-session client fixture

**Status: authored; both native producer builds and all runtime evidence pending.**
This fixture adds the same-session/different-viewport boundary absent from the
separate-session interactive fixture. It does not change that fixture, the
seven owner SSpec scenarios, product source or the frozen compiler cohort.

Source: `test/fixtures/compiler_entrypoint/windows_smux_shared_clients/main.spl`.
Sole argument: the actual compiled `smux.exe` for the producer under review.
Expected successful stdout is `Windows smux shared clients PASS` plus newline;
the adjacent golden `expected.stdout` is not observed execution evidence.

## Admission and required evidence

Build this standalone fixture with each admitted Phase 2 and Phase 3 producer,
then run against its matching actual compiled product. The application and
fixture must select native Windows TCP/ConPTY/console owners through the stable
configured interfaces. Wrong host, missing application, portable unsupported
resize/exit status, absent child output, rejected real resize or incomplete
cleanup must fail. No interpreter, seed, shell substitute or local service state
can satisfy the external-process fixture.

Use an external Windows Job/process-tree watchdog of at most 180 seconds and
retain its timeout/termination receipt. Native FFI nonreturn is outside the
source polling bounds. Preserve exact source and producer identities, both
executable hashes, configured-variant/runtime receipts, commands, stdout/stderr,
actual exit status and complete owned-tree cleanup evidence for each row.

| Producer cohort | fixture build | matching product | runtime/watchdog/cleanup |
|---|---|---|---|
| Phase 2 | Pending | Pending | Pending |
| Phase 3 | Pending | Pending | Pending |

## Manual workflow

1. Open three native ConPTY leases and launch the real `--serve` owner under
   one. Create exactly one shared session with a genuine pane shell using
   authenticated RPC. Open two actual `--attach` processes on this same session:
   small is 80x24 and large is 100x30.
2. Type a variable-setting command and echo through the small client's terminal
   input. Require the expanded `SMUX_SHARED_READY` output in **both** actual
   terminal streams, establishing shared content with independently running
   render clients. Require the explicit production frame header to be 80x24,
   the minimum attached canvas, and both client processes still alive.
3. Resize the small client's real ConPTY to 60x18 with the stable PTY resize API.
   Require the production frame to change to 60x18 while both actual clients
   remain alive. The fixture never calls `client-size` or layout RPC to simulate
   detection; the client console owner must observe the actual resize itself.
4. Send Ctrl-B `%` through small. Require two genuine panes, with small now
   selecting the new pane while large stays on the original pane. Type distinct
   variable values and echo commands through each client. Both views share the
   window and must show both expanded results. Query production explicit-pane
   history to require the large result only in the original pane and the small
   result only in the new pane. This proves independent input destinations even
   when another client's selected pane and cursor differ.
5. Send Ctrl-B `c` through small. It moves to a new window while large remains
   on the original window and pane. Type a command through small and require its
   fresh new-window marker only in small's terminal. Then type a fresh command
   through large and require the old pane's retained value only in large's
   terminal. Require the new window's actual frame also to use 60x18. Global
   service focus must not redirect either client's explicit window/pane input.
6. Send Ctrl-B `d` through small and require the actual client to terminate with
   retained-handle exit code zero. Require owner and large client still alive.
   Query both windows' production frames: both must expand to 100x30, reflecting
   removal of the smaller attachment, rather than leaving a stale minimum.
7. Through large, launch a real PowerShell child that computes
   `SMUX_INTERRUPT_42` and then sleeps for 120 seconds. Require that readiness
   output in large's actual terminal before injecting raw byte `0x03` (Ctrl-C).
8. Type another command through large to echo its original pane-owned value.
   Require computed `SMUX_AFTER_LARGE` in large's terminal within less than
   5000 monotonic milliseconds from Ctrl-C. It must remain absent from the
   detached small stream and the other window's explicit history. Require it
   in the original pane's actual history, with owner and large client alive.
   Without interruption, the sleeping child prevents the original shell from
   executing this command within the deadline.
9. Detach large using Ctrl-B `d` and require its actual retained-handle exit code
   zero while the owner remains running. Request authenticated server shutdown,
   require real owner exit zero, close all acquired leases with finite retries,
   and require `cleanup_pending() == 0` before printing the PASS line.

Expanded output markers are absent from injected command text. Distinct markers
for each phase prevent old output, local input echo or an earlier frame from
satisfying later checks. RPC observes frames/history and creates the initial
session; interactive changes and child input always traverse actual clients.

## Bounds and limitations

Input delivery and terminal output/exit waits permit at most 500 attempts with
10 ms sleeps. RPC inventories/frame geometry permit 100 attempts plus production
transport deadlines. Lease close permits 200 attempts with 10 ms sleeps. Client
output is retained with a 1-MiB cap per stream; overflow fails rather than
discarding possible routing evidence. A mandatory outer watchdog complements
these finite source bounds. Any earlier failure reaches all acquired-lease
cleanup before the final failure report; forced teardown is not a normal PASS.

The test observes actual raw ConPTY render output and exact frame dimensions;
it does not claim screenshot pixel fidelity or exhaustive cursor shape/style
coverage. Independent input destinations, selected windows/panes and retained
shell state are the cursor-related behavioral oracle. Console mode restoration
has its own native fixture. Clipboard requires its explicitly separate manual
gate. Nonreading-child fairness remains covered by the owner SSpec, not this
same-session fixture.

Failure groups are fixture admission (1-4), shared startup/canvas (10-22), local
pane input (23-30), independent window selection (31-40), minimum-client detach
and remaining viewport expansion (41-46), raw Ctrl-C/continuity (47-59), and
owner shutdown plus all-lease cleanup (60-66). No failure or PASS was observed:
both producer/runtime rows remain pending.
