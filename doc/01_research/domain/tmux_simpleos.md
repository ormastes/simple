<!-- codex-research -->
# Domain Research — `tmux_simpleos`

Date: 2026-04-24

## Sources

- tmux upstream repository: https://github.com/tmux/tmux
- tmux install documentation: https://github.com/tmux/tmux/wiki/Installing
- tmux control mode documentation: https://github.com/tmux/tmux/wiki/Control-Mode
- tmux FAQ: https://github.com/tmux/tmux/wiki/FAQ

## Findings

### 1. tmux is not just a binary loader problem

The upstream project describes tmux as a terminal multiplexer with detachable
sessions and a client/server architecture. It is not only a CLI utility; it is
an always-on session manager that coordinates clients, panes, window state,
terminal sizing, and pane output routing.

Impact for SimpleOS:

- Loading the executable bytes from a filesystem is only the first step.
- The OS must still provide terminal/process semantics close enough for tmux to
  operate correctly at runtime.

### 2. Upstream build dependencies are Unix-terminal oriented

The tmux installation docs list these core dependencies:

- `libevent`
- `ncurses`
- a C toolchain and build tooling

This matters because a stock port is not a self-contained pure-C binary in
practice; its behavior depends on terminal capability handling and event-loop
integration around traditional Unix facilities.

Impact for SimpleOS:

- A binary-hosting route requires either:
  - enough POSIX compatibility for tmux plus its dependencies, or
  - a custom repackaging/static build strategy and compatible runtime ABI.

### 3. Control mode is the cleanest behavior to emulate first

The official control-mode docs define a text protocol where a tmux client talks
to the tmux server using command blocks plus notifications such as pane output
events. The docs emphasize:

- command blocks with begin/end markers
- structured listing commands
- pane output notifications
- explicit client-size updates

Impact for SimpleOS:

- A Simple-native implementation does **not** need to reproduce the full
  internal architecture first.
- The most leverage comes from implementing a compatible or tmux-inspired
  control plane:
  - create session/window/pane
  - send input
  - capture output
  - resize client/pane
  - list/query state

This aligns well with the repo’s existing REST and dashboard contracts.

### 4. tmux depends heavily on terminal correctness

The FAQ highlights several terminal-sensitive areas:

- correct `TERM` handling via terminfo
- UTF-8 locale support
- escape-sequence timing and key decoding
- mouse behavior
- scrollback behavior tied to multi-pane multiplexing

Impact for SimpleOS:

- An unmodified stock tmux needs more than pipes and process spawn.
- It needs a sufficiently correct terminal environment and terminal capability
  model.

This is the biggest risk for the stock-binary path.

### 5. Native reimplementation can target a smaller acceptance bar

Because tmux’s externally useful model is session/window/pane orchestration,
SimpleOS does not need to begin with full upstream parity.

A first native implementation can intentionally narrow scope to:

- persistent sessions
- split panes
- shell per pane
- attach/detach
- capture and send input
- resize propagation

Deferred features can include:

- full key-table compatibility
- copy mode parity
- mouse parity
- config-language parity
- complete control-mode compatibility

## Domain Conclusion

The domain evidence supports this ranking:

1. **Best first step:** native Simple multiplexer with tmux-like API and model
2. **Second step:** compatibility adapter for the existing `std.tmux` and
   dashboard API shapes
3. **Later step:** try stock tmux binary hosting only after SimpleOS exposes
   a stronger PTY/TTY/process compatibility layer

In short:

- `tmux` is simple enough to **reimplement partially** in Simple.
- It is **not** simple enough to assume that “filesystem binary loading” alone
  will make the upstream binary work inside SimpleOS.
