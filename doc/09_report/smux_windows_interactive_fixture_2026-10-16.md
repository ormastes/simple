# Windows smux actual interactive-client fixture

**Status: authored; native build, execution and producer qualification pending.**
This is a live-host fixture/manual, not a PASS, generated SSpec receipt or
substitute for the existing seven independent-owner SSpec scenarios.

Source: `test/fixtures/compiler_entrypoint/windows_smux_interactive/main.spl`.
Expected successful stdout: `Windows smux interactive PASS` followed by newline.
The adjacent `expected.stdout` records that golden output, not observed evidence.

## Required products and execution boundary

Build the application entry `src/app/hosted_apps/smux_client.spl` and this fixture
separately with the admitted Phase 2 producer, then with the admitted Phase 3
producer. Supply the actual matching compiled `smux.exe` as the fixture's sole
argument. Preserve source identity, producer hash, runtime/provider identity,
configured-variant selection receipt, both executable hashes, exact commands,
exit status, stdout/stderr and watchdog receipt for each cohort.

The stable `std.sys.pty` import must resolve to the native Windows overlay.
The application must also select native Windows TCP, ConPTY and console owners.
Portable unsupported resize/exit-code APIs, a wrong host, a missing executable,
unavailable console access or failed child output cannot produce fixture PASS.
No Rust seed, interpreter fixture or test server is admissible execution proof.

Run under an external Windows Job/process-tree watchdog of at most 180 seconds.
Its timeout must fail and terminate the complete owned tree. Finite source loops
do not certify that a broken native FFI call returns. No watchdog run has occurred.

| Producer cohort | smux build | fixture build | execution and cleanup proof |
|---|---|---|---|
| Phase 2 | Pending | Pending | Pending |
| Phase 3 | Pending | Pending | Pending |

## Manual workflow

1. Acquire three independent native ConPTY leases: an 80x24 owner terminal, an
   80x24 alpha client terminal and a 100x30 beta client terminal. Launch the real
   compiled `--serve` process in the first lease. Bounded authenticated RPC
   checks establish readiness and create separate alpha/beta sessions, each
   with a genuine child shell. RPC does not synthesize either rendering client.
2. Launch two actual compiled `--attach` processes under the other two leases.
   Inject variable-setting and echo commands through each client's terminal
   input. Require `SMUX_ALPHA_READY` in alpha's observed terminal output and
   `SMUX_BETA_READY` in beta's. Exclude the other session's marker in each stream.
   Those expanded tokens are absent from injected commands, so local input echo
   alone cannot satisfy the checks.
3. Send Ctrl-B `%` to alpha. Query the explicit-window pane inventory until it
   contains two panes. Type another command through alpha and require output
   produced by the new shell. Beta must not show that output.
4. Send Ctrl-B Space twice. The controller cycles tiled -> even-horizontal ->
   even-vertical. Require the original 80x24 window's two rectangles to become
   `(0,0,80,12)` and `(0,12,80,12)`. Two key sequences force an observable
   geometry change; tiled and even-horizontal alone are equivalent for two panes.
5. Send Ctrl-B `c`. Require two actual windows, then type a command through
   alpha and require the new window's child-generated marker. Send Ctrl-B `n`
   to return to the original window and require the original shell variable.
6. Send Ctrl-B `d` to alpha. Require the actual attached client process to become
   terminal and query its retained process handle through `pty.exit_code` before
   closing the lease; exit code must be zero. The owner and beta client must
   remain alive, and the server must still report two sessions.
7. Type a fresh command through beta and require its original child variable to
   expand in beta's actual terminal output. Alpha must not receive that output.
   Detach beta using Ctrl-B `d`, require its process terminal and exit code zero,
   and require the owner still running.
8. Request authenticated owner shutdown, observe its actual process exit and
   require exit code zero. Close all three acquired leases with finite retries,
   and require provider `cleanup_pending() == 0`. Every acquired lease reaches
   this cleanup path even when an earlier check returns a failure code.
9. Only after cleanup, print the single PASS line and return zero. Any earlier
   failure is preserved through cleanup and prints `Windows smux interactive
   FAIL <code>` with a nonzero result.

## Bounds and limits

Each terminal send and output/exit wait permits at most 500 attempts with 10 ms
sleeps. Owner/pane/window readiness permits 100 attempts; each RPC also has the
production transport's finite request deadline. Each lease close permits 200
attempts with 10 ms sleeps. These bounds are complemented by the mandatory
external watchdog, rather than advertised as a combined 180-second source bound.

Observed alpha/beta output is retained up to 1 MiB per stream; overflow fails
instead of dropping bytes that could hide cross-client routing. Raw ConPTY
output is the rendering observation: this fixture does not claim screenshot
pixel fidelity, mouse behavior, all copy-mode interactions, same-session local
viewport independence, or full tmux compatibility. Both clients deliberately
use separate sessions as requested. The owner SSpec separately covers history
and nonreading-child input fairness.

Failure groups are argument/host/provider admission (1-4), startup and independent
client output (10-21), split/layout (22-28), windows and retained shell state
(29-37), detach/sibling continuity and real exit codes (38-49), and owner shutdown
and complete lease cleanup (50-56). No actual failure code or PASS has been
observed in this lane; both producer rows remain pending.
