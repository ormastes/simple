# REPL Backspace Indentation Test

## Current Implementation

The REPL has been updated with these key handlers:

1. **Tab Key** → Inserts 4 spaces
2. **Backspace Key** → Smart deletion:
   - If line contains only spaces before cursor: Delete ALL spaces
   - Otherwise: Delete one character
3. **Ctrl+U** → Delete up to 4 spaces (dedent)

## How to Test

### Start the REPL
```bash
./target/debug/simple
```

### Test 1: Tab inserts 4 spaces
1. Press Tab
2. Expected: Should insert 4 spaces (you'll see cursor move right)

### Test 2: Backspace on indent-only line
1. Press Tab (adds 4 spaces)
2. Press Backspace
3. **Expected**: All 4 spaces should be deleted at once
4. **Previous behavior**: Only 1 space deleted at a time

### Test 3: Backspace with text
1. Type: `    hello` (Tab then "hello")
2. Press Backspace
3. **Expected**: Should delete 'o' (one character)
4. Press Backspace 4 more times to delete "hell"
5. Now line has only spaces
6. Press Backspace
7. **Expected**: Should delete all 4 spaces at once

### Test 4: Ctrl+U dedent
1. Press Tab twice (8 spaces)
2. Press Ctrl+U
3. **Expected**: Deletes 4 spaces
4. Press Ctrl+U again
5. **Expected**: Deletes remaining 4 spaces

## Example Test Session

```
Simple Language v0.1.0 - Interactive Mode
Type expressions to evaluate. Use 'exit' or Ctrl-D to quit.

>>> [Press Tab]
>>>     [cursor here - 4 spaces inserted]
>>> [Press Backspace]
>>> [cursor here - all spaces deleted if working]
```

## Known Issues

The backspace handlers are registered using rustyline's `bind_sequence`, but:
- Terminal emulators may intercept backspace before rustyline sees it
- Some terminals send different codes for backspace (DEL vs ^H)
- The default rustyline bindings may take precedence

## Implementation Details

Located in: `src/driver/src/cli/repl.rs`

Key handlers:
- `PythonBackspaceHandler` (lines 51-71)
- `TabHandler` (lines 41-48)
- `DedentHandler` (lines 74-96)

Bindings registered (lines 237-258):
- KeyEvent::from('\t') → TabHandler
- KeyEvent::ctrl('u') → DedentHandler
- KeyEvent(KeyCode::Backspace, Modifiers::NONE) → PythonBackspaceHandler

## Alternative: Console Wrapper

If the direct key bindings don't work due to terminal limitations, we have implemented a PTY-based console wrapper that can intercept and transform backspace keys at a lower level.

See:
- `simple/examples/console_wrapper.spl`
- `simple/std_lib/src/spec/console/__init__.spl`
