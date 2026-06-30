# Backspace Indentation Fix - Research & Implementation

## Research: How Other Rust Tools Handle Indentation

### 1. Reedline (nushell's line editor)

**Modern alternative to rustyline:**
- Cleaner API with `EditCommand` enum
- Direct keybinding system
- Active development (used by nushell)
- Example: `EditCommand::BackspaceWord` for word deletion

**Resources:**
- [GitHub: nushell/reedline](https://github.com/nushell/reedline)
- [Docs: docs.rs/reedline](https://docs.rs/reedline/latest/reedline/)
- [Example usage](https://github.com/perlindgren/reedline-repl-rs)

### 2. Rustyline Official Examples

Found the definitive pattern in [custom_key_bindings.rs](https://github.com/kkawakam/rustyline/blob/master/examples/custom_key_bindings.rs):

```rust
struct TabEventHandler;
impl ConditionalEventHandler for TabEventHandler {
    fn handle(&self, evt: &Event, n: RepeatCount, _: bool, ctx: &EventContext) -> Option<Cmd> {
        // Check context before cursor
        if ctx.line()[..ctx.pos()]
            .chars()
            .next_back()
            .filter(|c| c.is_whitespace())
            .is_some()
        {
            Some(Cmd::SelfInsert(n, '\t'))
        } else {
            None  // Use default behavior
        }
    }
}
```

**Key Pattern:**
- Return `Some(Cmd)` to override behavior
- Return `None` to use default behavior
- Use `ctx.line()` and `ctx.pos()` for state access

### 3. Python REPL Behavior (Reference)

Standard behavior from [Python IDLE](https://bugs.python.org/issue41608):
- **In leading whitespace**: Delete one indent level (4 spaces)
- **After text**: Delete one character (default)
- **Empty indented line**: Remove one indent at a time

## Our Implementation Fix

### Problem with Original Code

```rust
// ❌ WRONG: Always returned Some, fighting with default bindings
fn handle(&self, ...) -> Option<Cmd> {
    if in_whitespace {
        return Some(Cmd::Kill(Movement::BackwardChar(all_spaces)));
    }

    // This fights with rustyline's default backspace!
    Some(Cmd::Kill(Movement::BackwardChar(1)))
}
```

### Fixed Implementation

```rust
// ✅ CORRECT: Return None to use default behavior
fn handle(&self, ...) -> Option<Cmd> {
    if in_leading_whitespace {
        let spaces_to_delete = min(4, spaces_count);
        return Some(Cmd::Kill(Movement::BackwardChar(spaces_to_delete)));
    }

    // Let rustyline handle normal backspace
    None
}
```

### Changes Made:
1. **Delete 4 spaces at a time** (one indent level) instead of all spaces
2. **Return `None`** for default behavior instead of manually handling single char
3. **Clearer logic**: Only override when in leading whitespace

## Testing

### Manual Test
```bash
./target/debug/simple

# Test 1: Press Tab → should insert 4 spaces
>>> [Tab]
>>>     [cursor]

# Test 2: Press Backspace → should delete 4 spaces
>>> [Backspace]
>>> [cursor at start]

# Test 3: Tab → "hello" → Backspace → should delete 'o'
>>>     hello[cursor]
>>> [Backspace]
>>>     hell[cursor]

# Test 4: Ctrl+U also works for dedent
>>>         [8 spaces, cursor]
>>> [Ctrl+U]
>>>     [4 spaces remain]
```

### Expected Behavior

| Scenario | Key | Result |
|----------|-----|--------|
| Only spaces before cursor | Backspace | Delete 4 spaces (1 indent) |
| 1-3 spaces before cursor | Backspace | Delete all remaining spaces |
| Text exists before cursor | Backspace | Delete 1 character (default) |
| Mixed (spaces then text) | Backspace | Delete 1 character (default) |

## Alternative: Switch to Reedline

If rustyline continues to have issues, consider migrating to reedline:

**Pros:**
- Modern, actively maintained
- Used by nushell (battle-tested)
- Cleaner API
- Better documentation

**Cons:**
- Migration effort
- Different API patterns
- Less mature than rustyline

## References

- [Rustyline Repository](https://github.com/kkawakam/rustyline)
- [Rustyline Custom Bindings Example](https://github.com/kkawakam/rustyline/blob/master/examples/custom_key_bindings.rs)
- [Reedline Repository](https://github.com/nushell/reedline)
- [Reedline Documentation](https://docs.rs/reedline/latest/reedline/)
- [Python IDLE Backspace Issue](https://bugs.python.org/issue41608)
- [LightTable Python: Intelligent Backspace](https://github.com/LightTable/Python/issues/36)

## Implementation Location

- File: `src/driver/src/cli/repl.rs`
- Handler: `PythonBackspaceHandler` (lines 50-77)
- Binding: Line 251-254
- Tested: 2025-12-27
