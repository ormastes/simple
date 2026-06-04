<!-- codex-research -->
# Feature Requirements — `tmux_simpleos`

Date: 2026-04-24
Selected option: `C`

## Goal

Provide a SimpleOS-native terminal multiplexer first, while shaping its API and
state model so a future stock-`tmux` backend can be introduced later without
breaking callers.

## Functional Requirements

### REQ-001 Session Model

The system shall provide persistent multiplexer sessions, each containing one or
more windows and panes.

### REQ-002 Pane-Backed Shells

Each pane shall host an interactive shell process or shell-compatible command
loop using existing SimpleOS shell/runtime facilities.

### REQ-003 Attach / Detach

Clients shall be able to attach to and detach from an existing session without
destroying session state.

### REQ-004 Split and Layout Operations

The system shall support creating panes by splitting an existing view and shall
track pane geometry for resize and rendering.

### REQ-005 Input and Output Routing

The system shall route user input to a selected pane and expose pane output for
interactive display, capture, and remote/dashboard consumption.

### REQ-006 State Query API

The system shall expose query operations for:

- sessions
- windows
- panes
- pane dimensions
- active pane/window selection

### REQ-007 Capture API

The system shall expose pane capture operations sufficient to retrieve the
currently visible pane content and recent buffered output.

### REQ-008 Compatibility-Facing API Shape

The first native implementation shall preserve a compatibility-facing API shape
close to the existing repo model used by `std.tmux` and the dashboard tmux API:

- session/window/pane listing
- send input/text
- capture pane
- resize pane/client

### REQ-009 Native-First Backend

The initial implementation shall be native to SimpleOS and shall not require
the upstream `tmux` binary, `libevent`, or `ncurses` at runtime.

### REQ-010 Backend-Swap Readiness

The architecture shall separate:

- session/pane control contract
- transport/API surface
- backend execution implementation

so a later stock-`tmux` backend can be added behind the same control contract.

### REQ-011 Failure Handling

The system shall fail explicitly and non-fatally for:

- missing shell executable
- invalid session/window/pane targets
- failed split/create operations
- unsupported resize targets

### REQ-012 Initial Scope Boundary

The first release may defer full parity for:

- copy mode
- mouse parity
- upstream key-table compatibility
- full tmux config-language compatibility
- complete control-mode protocol compatibility

## Out of Scope for This Phase

- running unmodified upstream `tmux` inside SimpleOS
- full POSIX PTY/TTY compatibility work beyond what the native multiplexer needs
- complete upstream tmux feature parity
