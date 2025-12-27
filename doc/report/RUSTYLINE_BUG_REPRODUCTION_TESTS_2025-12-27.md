# rustyline REPL Backspace Bug - Reproduction Tests

**Date:** 2025-12-27
**Status:** ✅ **BUG CONFIRMED AND DOCUMENTED**
**Test File:** `src/driver/tests/rustyline_repl_backspace_bug_test.rs`

---

## Summary

Created comprehensive E2E test suite that reproduces and documents the rustyline backspace limitation. All tests use PTY (pseudo-terminal) to simulate actual user interaction with the REPL.

**Bug:** When backspace is pressed after Tab (which inserts 4 spaces), only 1 space is deleted instead of all 4.

**Root Cause:** rustyline's `Movement::BackwardChar(n)` gets overridden by `movement.redo(event_repeat_count)`, replacing our `n=4` with `event_repeat_count=1`.

---

## Test Results

### ✅ All 4 Tests Passing

```
test test_rustyline_backspace_bug_reproduction ... ok
test test_rustyline_tab_behavior ... ok
test test_rustyline_multiple_tabs_and_backspaces ... ok
test test_rustyline_backspace_after_text ... ok
```

---

## Test Descriptions

### Test 1: `test_rustyline_backspace_bug_reproduction`

**Purpose:** Main bug demonstration with clear output

**Steps:**
1. Start rustyline REPL (default, no `--tui` flag)
2. Press Tab → 4 spaces inserted
3. Press Backspace → **Only 1 space deleted** ❌
4. Press Backspace 3 more times → All spaces deleted (workaround)

**Output:**
```
╔════════════════════════════════════════════════════════╗
║  BUG REPRODUCTION: rustyline Backspace Limitation     ║
╚════════════════════════════════════════════════════════╝

=== Step 1: Press Tab (expect 4 spaces inserted) ===
After Tab: \r\u{1b}[K>>>     \r\u{1b}[8C

=== Step 2: Press Backspace (expect 4 spaces deleted) ===
After Backspace: \r\u{1b}[K>>>    \r\u{1b}[7C

=== Analysis ===
❌ BUG CONFIRMED: Backspace only deleted 1 space
   Expected: All 4 spaces deleted
   Actual: 3 spaces remain (rustyline limitation)

   Root cause: rustyline's Movement::BackwardChar(4)
               gets overridden to BackwardChar(1) by
               movement.redo(event_repeat_count)

   Solution: Use TUI REPL with --tui flag
```

**Evidence:**
- After Tab: `>>>     ` (prompt + 4 spaces)
- After Backspace: `>>>    ` (prompt + 3 spaces) → Only 1 deleted!

---

### Test 2: `test_rustyline_tab_behavior`

**Purpose:** Verify Tab key correctly inserts 4 spaces

**Steps:**
1. Press Tab
2. Capture terminal output
3. Verify 4 spaces were inserted

**Result:**
```
Pressing Tab...
Output after Tab:
  Raw: [13, 27, 91, 75, 62, 62, 62, 32, 32, 32, 32, 32, 13, 27, 91, 56, 67]
  Display: \r\u{1b}[K>>>     \r\u{1b}[8C
✅ Tab correctly inserts 4 spaces
```

**Analysis:** Raw bytes show 4 space characters (32, 32, 32, 32) after prompt.

---

### Test 3: `test_rustyline_multiple_tabs_and_backspaces`

**Purpose:** Demonstrate bug with multiple indents

**Steps:**
1. Press Tab twice → 8 spaces total
2. Press Backspace once → Should delete 4, actually deletes 1

**Output:**
```
Pressing Tab twice (expect 8 spaces)...
After 2 Tabs: \r\u{1b}[K>>>         \r\u{1b}[12C

Pressing Backspace once (expect 4 spaces deleted)...
After 1 Backspace: \r\u{1b}[K>>>        \r\u{1b}[11C

Analysis:
  Spaces remaining: ~8
  ❌ BUG: Only 1 space deleted (7 remain)
```

**Evidence:**
- After 2 Tabs: Cursor at column 12 (prompt=4 + 8 spaces)
- After Backspace: Cursor at column 11 (prompt=4 + 7 spaces) → Only 1 deleted!

---

### Test 4: `test_rustyline_backspace_after_text`

**Purpose:** Verify normal backspace behavior is NOT affected

**Steps:**
1. Press Tab (4 spaces)
2. Type "hello"
3. Press Backspace → Should delete only 'o' (normal behavior)

**Output:**
```
Pressing Tab + typing 'hello'...
After Tab + 'hello': hello

Pressing Backspace (should delete only 'o')...
After Backspace: \r\u{1b}[K>>>     hell\r\u{1b}[12C
✅ Backspace correctly deleted only 1 character after text
```

**Analysis:** Backspace works normally when NOT in leading whitespace. This confirms the bug is specific to the smart backspace implementation in leading whitespace.

---

## Technical Details

### PTY Testing Infrastructure

**Helper Class: `PtySession`**
```rust
struct PtySession {
    reader: Box<dyn Read + Send>,
    writer: Box<dyn Write + Send>,
}

impl PtySession {
    fn new(use_tui: bool) -> Result<Self, Box<dyn std::error::Error>>
    fn send_tab(&mut self) -> Result<(), Box<dyn std::error::Error>>
    fn send_backspace(&mut self) -> Result<(), Box<dyn std::error::Error>>
    fn send_key(&mut self, key: &[u8]) -> Result<(), Box<dyn std::error::Error>>
    fn read_output(&mut self, wait_ms: u64) -> Result<String, Box<dyn std::error::Error>>
}
```

**Key Features:**
- Spawns REPL in real pseudo-terminal
- Sends actual keyboard events (Tab = `\t`, Backspace = `\x7f`)
- Captures ANSI escape sequences
- Configurable for rustyline vs TUI mode

### ANSI Escape Sequence Analysis

**After Tab:**
```
\r\u{1b}[K>>>     \r\u{1b}[8C
 │   │      │       │
 │   │      │       └─ Move cursor to column 8 (prompt + 4 spaces)
 │   │      └─────── 4 space characters (32, 32, 32, 32)
 │   └──────────── Clear line (ESC[K)
 └──────────────── Carriage return
```

**After Backspace (bug):**
```
\r\u{1b}[K>>>    \r\u{1b}[7C
 │   │      │      │
 │   │      │      └─ Move cursor to column 7 (only -1)
 │   │      └───────── 3 space characters (32, 32, 32) - only 1 deleted!
 │   └──────────── Clear line
 └──────────────── Carriage return
```

---

## Root Cause Analysis

### The Problem

When we try to implement smart backspace in rustyline:

```rust
// In our custom handler (src/driver/src/cli/repl.rs)
fn handle_backspace() -> Cmd {
    // We want to delete 4 spaces
    Cmd::Kill(Movement::BackwardChar(4))
}
```

But rustyline internally does:

```rust
// Inside rustyline library (external code)
impl Movement {
    fn redo(&self, repeat_count: Option<usize>) -> Movement {
        match *self {
            Movement::BackwardChar(n) => {
                // Our n=4 gets REPLACED by repeat_count=1!
                Movement::BackwardChar(repeat_count.unwrap_or(1))
            }
            // ...
        }
    }
}
```

**Result:** Our `BackwardChar(4)` becomes `BackwardChar(1)`.

### Why TUI Works

TUI implementation bypasses rustyline entirely:

```rust
// In src/driver/src/cli/tui/editor.rs
EditorAction::Backspace => {
    let spaces_to_delete = 4;

    // Direct buffer manipulation - no library override!
    for _ in 0..spaces_to_delete {
        self.buffer.remove(prev_char_idx);
        self.cursor = prev_char_idx;
    }
}
```

No `Movement` abstraction → Full control → Bug doesn't exist!

---

## Running the Tests

### Run All Bug Reproduction Tests
```bash
cargo test --test rustyline_repl_backspace_bug_test -- --nocapture
```

### Run Individual Tests
```bash
# Main bug demonstration
cargo test --test rustyline_repl_backspace_bug_test test_rustyline_backspace_bug_reproduction -- --nocapture

# Tab behavior verification
cargo test --test rustyline_repl_backspace_bug_test test_rustyline_tab_behavior -- --nocapture

# Multiple tabs/backspaces
cargo test --test rustyline_repl_backspace_bug_test test_rustyline_multiple_tabs_and_backspaces -- --nocapture

# Backspace after text
cargo test --test rustyline_repl_backspace_bug_test test_rustyline_backspace_after_text -- --nocapture
```

---

## Workaround

### For Users

**Use TUI REPL instead of default REPL:**

```bash
# Build with TUI feature
cargo build --release --features tui

# Run TUI REPL (backspace works!)
./target/release/simple --tui
```

**In TUI mode:**
```python
>>> [Press Tab]
>>>     ____  ← 4 spaces

>>> [Press Backspace]
>>>  ← All 4 spaces deleted! ✅
```

### For Default REPL

**Press backspace 4 times** to delete a full indent:

```python
>>> [Press Tab]
>>>     ____  ← 4 spaces

>>> [Press Backspace 4 times]
>>>  ← Need 4 presses to delete all spaces ❌
```

---

## Files Created

1. **`src/driver/tests/rustyline_repl_backspace_bug_test.rs`** (300+ lines)
   - 4 comprehensive E2E tests
   - PTY-based terminal simulation
   - Clear bug demonstration with analysis

---

## References

### Documentation
- **Root Cause Analysis:** `doc/research/REPL_BACKSPACE_LIMITATION.md`
- **TUI Implementation:** `doc/features/TUI_REPL.md`
- **TUI Completion Report:** `doc/report/TUI_REPL_BACKSPACE_COMPLETION_2025-12-27.md`
- **Expected Failure Tests:** `doc/report/EXPECTED_FAILURE_TESTS_2025-12-27.md`
- **PTY Testing Guide:** `doc/research/TERMINAL_SEQUENCE_CAPTURE.md`

### Test Files
- **Bug Reproduction:** `src/driver/tests/rustyline_repl_backspace_bug_test.rs` (this file)
- **Expected Failure Tests:** `src/driver/tests/rustyline_backspace_expected_failure_test.rs`
- **TUI E2E Tests:** `src/driver/tests/tui_repl_e2e_test.rs`
- **Comparison Test:** `src/driver/tests/repl_comparison_test.rs`

---

## Conclusion

### ✅ Bug Successfully Reproduced

All 4 tests pass and clearly demonstrate:
1. **Tab inserts 4 spaces** ✓
2. **Backspace only deletes 1 space** ❌ (BUG)
3. **Root cause identified** ✓ (rustyline's `movement.redo()` override)
4. **Workaround available** ✓ (TUI REPL with `--tui` flag)

These tests serve as:
- **Documentation** of the limitation
- **Regression tests** (ensure bug stays documented)
- **Verification** that TUI solution is necessary

---

**Test Status:** ✅ All Passing (4/4)
**Bug Status:** ❌ Confirmed in rustyline
**Solution Status:** ✅ TUI REPL available
