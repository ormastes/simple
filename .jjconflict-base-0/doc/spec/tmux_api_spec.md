# Tmux API Library Specification

*Source: `test/lib/std/unit/tmux/tmux_api_spec.spl`*
*Last Updated: 2026-03-29*

**Feature IDs:** #TMUX-001
**Category:** Stdlib
**Difficulty:** 2/5
**Status:** Implemented
**Requirements:** N/A
**Plan:** N/A
**Design:** N/A
**Research:** N/A

---

## Overview

Tests for the `std.tmux` module which provides a read/write interface
to the tmux terminal multiplexer. The module wraps tmux CLI commands
via `shell()` to list sessions, windows, panes, capture pane content,
and send keystrokes.

## Key Concepts

| Concept | Description |
|---------|-------------|
| TmuxSession | A named tmux session with windows count and attached state |
| TmuxWindow | A window within a session, identified by index |
| TmuxPane | A pane within a window, with dimensions and running command |
| TmuxCaptureResult | Content captured from a pane with row count |
| capture-pane | Reads visible content from a tmux pane |
| send-keys | Sends keystroke sequences to a tmux pane |

## Behavior

- All functions gracefully handle missing tmux or inactive server
- Listing functions return empty arrays when target doesn't exist
- Mutation functions return Result<T, text> for error handling
- Capture returns empty content for non-existent panes
- Struct types are plain data containers with no invariants

## Examples

```simple
use std.tmux.*

if tmux_available():
    val sessions = tmux_list_sessions()
    for s in sessions:
        print "Session: {s.name} ({s.windows} windows)"

    val capture = tmux_capture_pane("main", 0, 0)
    print capture.content
```

## Availability Detection

    Validates that tmux availability and server status checks
    return boolean values without crashing, regardless of whether
    tmux is actually installed on the test system.

## Session Listing and Lookup

    Tests session enumeration and existence checking.
    Returns empty results for non-existent sessions rather than errors.

### Scenario: Enumerating all active tmux sessions

        Should return a list of TmuxSession structs, or empty list
        if no tmux server is running.

### Scenario: Querying a non-existent session

        Should return false for sessions that don't exist,
        without raising errors.

## Window and Pane Enumeration

    Tests listing windows within a session and panes within a window.
    Non-existent targets should return empty lists.

### Scenario: Non-existent session

        Querying windows from a non-existent session returns empty list.

### Scenario: Non-existent session and window

        Querying panes from a non-existent target returns empty list.

## Capture Pane Content

    Tests the `tmux capture-pane` wrapper which reads visible
    terminal content from a pane. Non-existent targets return
    empty content with the formatted pane_id.

## Struct Construction and Field Access

    Validates that all tmux data types can be constructed with
    named fields and that field values are preserved correctly.

### Scenario: Session metadata

        TmuxSession holds name, window count, attached status, and creation time.

### Scenario: Window metadata

        TmuxWindow holds session reference, index, name, active flag, and pane count.

### Scenario: Pane metadata with dimensions and process info

        TmuxPane holds full target coordinates, dimensions, current command, and PID.

### Scenario: Captured pane content

        TmuxCaptureResult holds the text content, pane identifier, and row count.

## Test Summary

| Metric | Count |
|--------|-------|
| Scenarios | 12 |
| Slow Scenarios | 0 |
| Skipped Scenarios | 0 |

## Scenarios

- reports whether tmux is installed
- reports server running status
- returns a list without crashing
- returns false for non-existent session
- returns empty list for non-existent session
- returns empty list for non-existent target
- returns empty capture for non-existent target
- formats pane_id as session:window.pane
- constructs with all fields
- constructs with all fields
- constructs with all fields
- constructs with all fields
