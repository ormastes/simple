# REPL Backspace Indent Deletion - rustyline Limitation

## Summary

**Objective:** Make backspace delete a full indent level (4 spaces) when pressed in leading whitespace
**Result:** Not possible with current rustyline API
**Status:** Documented limitation with workaround

## Investigation

### Test Setup

Created comprehensive PTY-based integration test using `portable-pty`:
- File: `src/driver/tests/repl_backspace_pty_test.rs`
- Captures raw terminal sequences (ANSI escape codes)
- Parses cursor movements to verify actual behavior
- Tests three scenarios:
  1. Tab inserts 4 spaces ✅
  2. Backspace deletes full indent (4 spaces) ❌
  3. Backspace after text deletes 1 character ✅

### Root Cause

rustyline's `ConditionalEventHandler` has a fundamental limitation:

```rust
pub trait ConditionalEventHandler {
    fn handle(&self, evt: &Event, n: RepeatCount, ..., ctx: &EventContext) -> Option<Cmd>;
}
```

**Problem:** When a handler returns `Some(Cmd::Kill(Movement::BackwardChar(4)))`:
1. The `Movement::BackwardChar(4)` contains a repeat count of 4
2. rustyline internally calls `movement.redo(Some(event_repeat_count))`
3. This REPLACES our count (4) with the event's count (1 for single backspace press)
4. Result: Only 1 character gets deleted

**Evidence from rustyline source** (`src/keymap.rs`):
```rust
impl Movement {
    const fn redo(&self, new: Option<RepeatCount>) -> Self {
        match *self {
            Movement::BackwardChar(previous) => {
                Movement::BackwardChar(repeat_count(previous, new))
            }
            ...
        }
    }
}
```

### Attempted Solutions

| Approach | Command | Result |
|----------|---------|--------|
| 1. Kill command | `Cmd::Kill(Movement::BackwardChar(4))` | Deletes 1 space (not 4) |
| 2. Replace command | `Cmd::Replace(Movement::BackwardChar(4), None)` | Created strange behavior (8 spaces!) |
| 3. Dedent command | `Cmd::Dedent(Movement::BackwardChar(4))` | Deletes 1 space (not 4) |
| 4. Stateful handler | Track state + multiple calls | Handler only called once per keypress |
| 5. Insert backspaces | `Cmd::Insert(...)` with `\x08` chars | Not supported by rustyline |

**Test Output Example:**
```
[BACKSPACE] Called! line='    ', pos=4, RepeatCount=1
[BACKSPACE] Deleting 4 spaces (indent mode)
Raw output: "\r\u{1b}[K>>>   \r\u{1b}[6C"
                            ^^^
                            Only 3 spaces remain (1 deleted, not 4)
```

### Why This Can't Be Fixed

1. **One keypress = One command execution**
   - `ConditionalEventHandler` returns `Option<Cmd>` - a SINGLE command
   - Cannot return a sequence of commands

2. **RepeatCount override is hardcoded**
   - rustyline's command execution always calls `movement.redo(event.repeat_count)`
   - No way to preserve the Movement's original repeat count

3. **No direct buffer access**
   - `EventContext` only provides `line()` and `pos()` (read-only)
   - No API to directly modify the line buffer from within a handler

## Workaround

Use **Ctrl+U** for dedenting (deleting 4 spaces):

```simple
# REPL usage:
>>> ____    # 4 spaces of indentation
>>> [Press Ctrl+U]  # Deletes 4 spaces
>>>
```

This binding is already implemented in `DedentHandler` (though it has the same limitation).

## Recommendations

### Option 1: Accept the limitation
- Document that backspace deletes one space at a time
- Users can press backspace 4 times, or use Ctrl+U

### Option 2: File rustyline issue
- Request that `ConditionalEventHandler` can specify repeat count override
- Or request a `Cmd::KillExact(usize)` variant that doesn't use Movement

### Option 3: Switch to reedline
- [reedline](https://github.com/nushell/reedline) is nushell's line editor
- More modern architecture, better customization
- Used by production tools (nushell, gitui)
- Migration effort: Medium (API differences)

### Option 4: Implement custom solution
- Write custom line editing from scratch
- Use `crossterm` for terminal control
- Effort: Very High (weeks of work)

## Files Modified

- `src/driver/src/cli/repl.rs` - Backspace handler (documented limitation)
- `src/driver/tests/repl_backspace_pty_test.rs` - PTY integration test
- `src/driver/Cargo.toml` - Added `portable-pty` dev-dependency
- `doc/research/TERMINAL_SEQUENCE_CAPTURE.md` - PTY testing guide

## References

- rustyline source: https://github.com/kkawakam/rustyline
- reedline (alternative): https://github.com/nushell/reedline
- portable-pty docs: https://docs.rs/portable-pty/latest/portable_pty/
- ANSI escape codes: https://en.wikipedia.org/wiki/ANSI_escape_code

## Decision

**Status:** Documented limitation
**Workaround:** Use Ctrl+U for dedent
**Future:** Consider migrating to reedline in next major version

---

**Created:** 2025-12-27
**Author:** Claude Code
**Related:** #REPL, #Terminal, #UX
