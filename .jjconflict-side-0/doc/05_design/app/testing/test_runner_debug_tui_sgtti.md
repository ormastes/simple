# Test Runner Debug TUI SGTTI Design

## Overview

`src/app/test_runner_new/test_runner_debug_tui.spl` is a pure model for
session-debug UI evidence. It converts an existing `SessionSchedule` into:

- stable TUI text lines
- a text capture string
- a WinText/SGTTI snapshot
- compact summary text for runner diagnostics

The normal test-runner entrypoints do not import this module. Tests and explicit
debug/evidence flows import it directly.

## Data Flow

```text
SessionSchedule
  -> test_runner_debug_tui_model
  -> test_runner_debug_tui_capture  -> build/test-artifacts/.../debug_tui.txt
  -> test_runner_debug_tui_snapshot -> SgttiTestDriver queries
```

## Zero-Overhead Boundary

SGTTI must not add default runtime overhead. The default entrypoints
`src/app/test_runner_new/main.spl` and `src/app/test_runner_new/test_runner_main.spl`
must not import `std.ui_test.sgtti`, `SgttiTestDriver`, or
`test_runner_debug_tui`. The debug TUI module imports only common WinText access
types, while the executable system spec imports SGTTI to verify visible state.

## Error Handling

The debug TUI model is deterministic and side-effect-free. Capture writing is
owned by the system spec so production code does not allocate or write evidence
artifacts.
