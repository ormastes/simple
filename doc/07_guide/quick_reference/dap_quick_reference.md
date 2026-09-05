# DAP Debugging Quick Reference

## Start with evidence

DAP is an IDE client of `DebugServiceV1`; the service owns mutable state and the
client uses `DebugSessionId`. Preserve the original log/dump/trace, then run
`simple debug doctor [profile.sdn]`. Blocked, unverified, and unavailable rows
are not passes even when adapter source exists.

Use D0–D12: intake → preserve → doctor → classify → budgets → cheapest decisive
observation → reproduce → hypothesis → receipted probe/attach → root-cause
owner → test decision → fix/verify → cleanup/knowledge. Reproduce external
behavior at System SSpec level, narrow the owning boundary with Integration
SSpec, and add Unit/property coverage only when justified. If either required
reproducer is unfaithful, resume debugging at that boundary; add adjacent
tests only after both are faithful.

## Keyboard Shortcuts

| Action | Windows/Linux | macOS | Description |
|--------|---------------|-------|-------------|
| **Start Debugging** | F5 | F5 | Launch debugger |
| **Stop Debugging** | Shift+F5 | Shift+F5 | Stop current session |
| **Restart Debugging** | Ctrl+Shift+F5 | Cmd+Shift+F5 | Restart from beginning |
| **Continue** | F5 | F5 | Resume execution |
| **Pause** | F6 | F6 | Pause at current line |
| **Step Over** | F10 | F10 | Execute line, don't enter functions |
| **Step Into** | F11 | F11 | Execute line, enter functions |
| **Step Out** | Shift+F11 | Shift+F11 | Execute until function returns |
| **Toggle Breakpoint** | F9 | F9 | Add/remove breakpoint |
| **Run to Cursor** | Ctrl+F10 | Cmd+F10 | Run until cursor line |

## Breakpoint Types

| Symbol | Type | How to Create |
|--------|------|---------------|
| 🔴 | Regular | Click gutter or press F9 |
| 💎 | Conditional | Right-click breakpoint → Edit |
| 📍 | Logpoint | Right-click line → Add Logpoint |
| ⏸️ | Disabled | Right-click breakpoint → Disable |

## Views

| View | Shortcut | Shows |
|------|----------|-------|
| **Variables** | - | Local & global variables |
| **Watch** | - | Custom expressions |
| **Call Stack** | - | Function call chain |
| **Breakpoints** | - | All breakpoints |
| **Debug Console** | Ctrl+Shift+Y | REPL for expressions |

## Debug Console Commands

```simple
# Evaluate expressions
> x + y
84

# Check variable types
> typeof(user)
"Struct"

# Call functions
> factorial(5)
120

# Inspect objects
> user
Struct { name: "Alice", age: 30 }
```

## Variable Display

| Icon | Type | Example |
|------|------|---------|
| 🔢 | Number | `42`, `3.14` |
| 📝 | String | `"Hello"` |
| ✓/✗ | Boolean | `true`, `false` |
| 📦 | Array | `[1, 2, 3]` |
| 🗂️ | Dict | `{"name": "Alice"}` |
| 🏗️ | Struct | `User { ... }` |
| 🎭 | Enum | `Some(42)` |
| ⚡ | Function | `<function factorial>` |

## Step Mode Behavior

### Step Over (F10)
```simple
fn main():
    val x = 5
    process(x)  # ← If you press F10 here
    print x     # ← Execution stops here (doesn't enter process)
```

### Step Into (F11)
```simple
fn main():
    val x = 5
    process(x)  # ← If you press F11 here
    print x
                # ↓ Execution enters process function
fn process(n):
    return n * 2  # ← Stops here
```

### Step Out (Shift+F11)
```simple
fn process(n):
    val result = n * 2  # ← If you press Shift+F11 here
    return result       # ← Executes this
                        # ↓ Returns to caller
fn main():
    val x = process(5)
    print x  # ← Stops here
```

## Conditional Breakpoints

### Value Comparison
```simple
x > 100
user.age >= 18
items.length == 0
```

### Complex Conditions
```simple
x > 10 and y < 20
user.name == "Alice" or user.is_admin
not items.is_empty()
```

### Hit Count
```
> 5        # Break after 5th hit
>= 10      # Break on 10th+ hit
% 5 == 0   # Break every 5th hit
```

## Common Patterns

### Debug Loop Iteration
```simple
for i in 0..100:
    val result = process(i)  # Set conditional breakpoint: i == 50
    save(result)
```

### Debug Error Handling
```simple
match result:
    case Ok(value):
        use_value(value)  # Breakpoint here to inspect success case
    case Err(error):
        log_error(error)  # Breakpoint here to inspect error
```

### Debug Async Code
```simple
val future = async {
    val data = await fetch_data()  # Breakpoint to see await resolution
    process(data)
}
```

## Performance Tips

✅ **DO:**
- Use conditional breakpoints to skip irrelevant hits
- Remove breakpoints when not needed
- Use "Continue" instead of stepping through long sections
- Set breakpoints close to the issue
- Prefer passive evidence or a log/trace/count probe before stopping execution

❌ **DON'T:**
- Leave breakpoints in tight loops (use conditions!)
- Step through library code unnecessarily
- Keep debug mode on in production
- Set too many breakpoints (slows down)

Every attach, probe, capture, control, and cleanup should emit a
`DebugReceiptV1` bound to the exact build. On completion record provider token
fields (or `unavailable`) per bug in the bug database. Usage above 2× the documented comparable bug-fix
average requires a linked reusable knowledge/skill/tool update before closure.

## Troubleshooting

### Breakpoint has gray circle (not hit)
**Cause:** Source file not loaded or path mismatch
**Fix:** Check file path, restart debugger

### Variables show "<unavailable>"
**Cause:** Optimized away or out of scope
**Fix:** Build in debug mode, check scope

### Stepping is slow
**Cause:** Too many breakpoints or expressions
**Fix:** Remove unused breakpoints, simplify watches

### Can't see value of variable
**Cause:** Variable not yet defined or already out of scope
**Fix:** Step to line after definition

## VS Code Settings

Add to `.vscode/settings.json`:

```json
{
  "debug.inlineValues": true,
  "debug.showInStatusBar": "always",
  "debug.toolBarLocation": "docked",
  "debug.console.fontSize": 14,
  "debug.console.lineHeight": 20
}
```

## Resources

- Full Guide: [DAP Debugging Guide](./dap_debugging_guide.md)
- Examples: [examples/debugging/](../../examples/debugging/)
- DAP Spec: https://microsoft.github.io/debug-adapter-protocol/
