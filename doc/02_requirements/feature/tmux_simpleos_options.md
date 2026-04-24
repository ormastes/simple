<!-- codex-research -->
# Feature Requirement Options — `tmux_simpleos`

Date: 2026-04-24

## Option A — Native Simple `tmux-lite` for SimpleOS

Description:
Implement a SimpleOS-native multiplexer service and app with tmux-like
sessions, windows, panes, attach/detach, pane input/output capture, and resize.

Pros:

- best fit for current repo capabilities
- reuses existing shell, SSH PTY, SPM/dashboard, and VFS/exec work
- avoids immediate dependency on full Unix PTY and terminal compatibility
- can preserve current `std.tmux` object model and dashboard API surface

Cons:

- not full upstream tmux parity
- requires new native session manager logic and UI integration
- some features such as copy mode, mouse parity, and config compatibility would
  be deferred

Effort:

- `L`
- estimated files: 12-18

## Option B — Host/Bundled Stock `tmux` Binary in SimpleOS

Description:
Bundle or install upstream tmux plus dependencies, load it from the SimpleOS
filesystem, and run it as an external binary.

Pros:

- maximum compatibility if it works
- no need to reimplement tmux feature logic

Cons:

- highest technical risk
- depends on PTY/TTY/session semantics that SimpleOS does not yet prove
- depends on runtime compatibility for `libevent`, `ncurses`, terminal
  capabilities, UTF-8 handling, and process behavior
- likely to fail late after substantial enablement work

Effort:

- `XL`
- estimated files: 20-35 plus dependency packaging/build work

## Option C — Hybrid: Native Multiplexer Now, Stock Binary Later

Description:
Implement a native SimpleOS multiplexer first, but shape its API so a future
stock-tmux backend can be swapped in when the OS compatibility layer matures.

Pros:

- best risk-adjusted path
- delivers value quickly
- preserves a migration path to upstream compatibility later
- aligns with the existing host-side `std.tmux` and REST contracts

Cons:

- more architecture work up front than Option A
- still does not deliver full upstream tmux immediately

Effort:

- `L`
- estimated files: 14-22

## Recommendation

Recommended option: **Option C**

Reason:

- It matches the current SimpleOS maturity level.
- It avoids betting the feature on missing Unix terminal semantics.
- It gives a clean path to later experiment with a real tmux binary without
  discarding the first implementation.
