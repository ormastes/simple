<!-- codex-design -->
# `tmux_simpleos` Architecture

Date: 2026-04-24
Related requirements:
- `doc/02_requirements/feature/tmux_simpleos.md`
- `doc/02_requirements/nfr/tmux_simpleos.md`

## Decision

SimpleOS will implement a native terminal multiplexer service, informally
`simplemux`, as the first backend for `tmux_simpleos`.

The architecture separates:

- control contract
- session state ownership
- pane execution backend
- transport/UI adapters

This keeps the first implementation native to SimpleOS while preserving a later
path to a stock-`tmux` backend.

## Why This Architecture

The repo already has:

- a mature shell surface (`ShellApp`)
- pipe-based PTY emulation (`SshPty`)
- executable resolution and process spawn surfaces
- tmux-shaped host API and dashboard contracts

The repo does **not** yet prove:

- general-purpose Unix PTY semantics
- controlling-terminal/session behavior
- enough terminal compatibility to treat stock `tmux` as a near-term runtime
  dependency

So the native backend is the lowest-risk architecture that still preserves
future compatibility.

## Layering

```text
Dashboard / terminal UI / SSH / future CLI adapters
                        |
                        v
simplemux control contract
                        |
                        v
simplemux session service
  - session registry
  - window registry
  - pane registry
  - pane buffers
  - attach table
                        |
                        v
pane backend
  - native ShellApp pane driver
  - native PTY bridge
  - future stock-tmux adapter
                        |
                        v
SOSIX / shell / process / VFS / window transport
```

## Module Ownership

Recommended ownership split:

- `src/os/apps/simplemux/contract.spl`
  - backend-agnostic control types and commands
- `src/os/apps/simplemux/service.spl`
  - authoritative session/window/pane state
- `src/os/apps/simplemux/backend_native.spl`
  - native ShellApp + PTY-backed pane execution
- `src/os/apps/simplemux/buffer.spl`
  - bounded pane capture ring / line buffer
- `src/os/apps/simplemux/layout.spl`
  - split tree and geometry computation
- `src/os/apps/simplemux/api.spl`
  - adapter-facing functions mirroring current tmux-shaped operations
- `src/app/web_dashboard/tmux_api.spl` or equivalent adapter
  - maps HTTP to the new control contract

## Core Data Model

### Session

Owns:

- stable session id and name
- attached client count
- current window id
- window list
- service-local generation counter

### Window

Owns:

- stable window id and index
- layout root
- pane ids
- active pane id
- title/name

### Pane

Owns:

- stable pane id and index
- geometry
- execution state
- shell/backend handle
- capture buffer
- last known cwd/command metadata when available

### Client Attachment

Owns:

- client id
- attached session id
- requested cols/rows
- last-seen active window/pane

Client attachments are ephemeral. Session/window/pane state is authoritative.

## Execution Model

### Native Backend

The native backend launches a pane around existing SimpleOS shell facilities.

Preferred first shape:

1. create per-pane PTY-style bridge
2. create shell instance bound to that bridge
3. route user input into pane backend
4. poll/drain pane output into a bounded capture buffer
5. expose current visible output and recent history through capture APIs

### Backend Boundary

Backends implement operations equivalent to:

- create pane
- destroy pane
- write input
- resize
- poll output
- report lifecycle state

This boundary is what enables a later stock-`tmux` backend experiment.

## Layout Model

Use a split-tree layout rather than storing panes only as a flat list.

Reasons:

- pane split operations become first-class
- resize propagation is deterministic
- window rendering and future GUI/TUI views can share one geometry model

Minimal node types:

- `Leaf(pane_id)`
- `SplitHorizontal(children, weights)`
- `SplitVertical(children, weights)`

## Capture Buffer Strategy

Each pane owns a bounded append-only output buffer suitable for:

- visible snapshot
- recent history capture
- reconnect / detach-reattach continuity

Policy:

- append output chunks from the backend
- maintain line-oriented indexing for capture
- evict oldest lines when pane budget is exceeded

This avoids full transcript rereads and satisfies the NFR hot-path constraint.

## Transport / Adapter Strategy

Adapters must not own session truth.

Adapters include:

- dashboard REST
- future native TUI
- future GUI panel
- SSH integration

They only:

- send control commands
- request state snapshots
- subscribe/poll output deltas

## Startup Path

Startup path for the first service:

1. initialize empty session registry
2. initialize backend factory
3. defer pane creation until first session/window request
4. avoid scanning filesystem or launching helper processes at startup

This keeps startup under the NFR budget.

## Hot Paths

Hot paths are:

- input routing to active pane
- output draining from pane backend
- capture reads
- resize propagation

Rules:

- no per-keystroke subprocess creation
- no per-keystroke file reads
- no full-session rescans for single-pane updates

## Invalidation / Cache Policy

State caches are service-owned and event-driven.

- session/window/pane registries are authoritative in memory
- pane capture buffers are incrementally updated from backend output
- layout is recomputed on split/close/resize only
- attachment state invalidates only on attach/detach/client-size change

No periodic rebuild of the full model is allowed in the steady-state path.

## Error Containment

Errors are isolated at pane and session boundaries.

- pane launch failure marks pane failed without crashing service
- missing shell/runtime returns explicit backend error
- invalid pane/session/window targets return typed failure
- one pane crash does not destroy other panes or sessions

## MDSOC Evaluation

This feature crosses multiple subsystems, but it does not currently justify a
separate MDSOC transform. The feature is better modeled as a native service with
adapters around it.

If later work adds policy overlays such as audit, collaboration, or remote
sharing across all panes/sessions, those may become MDSOC candidates.

## Observability

The service should expose counters/timings for:

- startup duration
- session create/destroy
- pane create/split/close
- input-to-output latency
- capture buffer size and eviction count

## Deferred Architecture Work

- stock-tmux backend adapter
- full control-mode protocol compatibility
- copy-mode parity
- mouse parity
- controlling-terminal/PTY subsystem promotion into a general OS service
