<!-- codex-design -->
# `tmux_simpleos` Agent Tasks

## Slice 1: Core Native Service

- add `src/os/apps/smux/contract.spl`
- add `src/os/apps/smux/service.spl`
- add `src/os/apps/smux/layout.spl`
- add `src/os/apps/smux/buffer.spl`
- define session/window/pane ids and state structs

## Slice 2: Native Backend

- add `src/os/apps/smux/backend_native.spl`
- adapt pipe-based PTY helper for pane execution
- bind `ShellApp` to pane backend I/O
- implement output drain and bounded capture

## Slice 3: Compatibility API

- add `src/os/apps/smux/api.spl`
- map tmux-shaped operations onto the native service
- preserve session/window/pane/capture response shape

## Slice 4: Adapters

- update dashboard tmux adapter to call native service
- optionally add terminal/TUI entry surface
- wire attach/detach and resize handling

## Slice 5: Verification

- add unit tests for layout, buffers, and service routing
- add system feature spec coverage for all REQs
- add latency/startup instrumentation checks where practical

## Deferred Slice

- stock-tmux backend adapter
- control-mode compatibility layer
- copy mode, mouse parity, config compatibility
