# Signal Handler SFFI Specification

**Purpose:** Enable Simple programs to register signal handlers for graceful shutdown

**Status:** SFFI specification (requires implementation in `seed/runtime.c`)

---

## Required SFFI Functions

### 1. rt_signal_handler_available()

**Signature:**
```c
bool rt_signal_handler_available();
```

**Purpose:** Check if signal handling is supported on this platform

**Returns:**
- `true` if signal handling is available
- `false` on Windows or if signals not supported

**Implementation:**
```c
bool rt_signal_handler_available() {
#ifdef _WIN32
    return false;  // Windows signal handling is different
#else
    return true;   // Unix/Linux/macOS support signals
#endif
}
```

---

### 2. rt_signal_handler_install()

**Signature:**
```c
void rt_signal_handler_install(int64_t signal, void (*handler)(void));
```

**Purpose:** Install a signal handler for the given signal

**Parameters:**
- `signal` - Signal number (POSIX standard: 1=SIGHUP, 2=SIGINT, 15=SIGTERM)
- `handler` - Simple function pointer (takes no args, returns nothing)

**Implementation:**
```c
#include <signal.h>

// Global table to store Simple handlers
static void (*simple_handlers[32])(void) = {NULL};

// C signal handler wrapper
static void c_signal_handler(int sig) {
    if (sig >= 0 && sig < 32 && simple_handlers[sig] != NULL) {
        // Call the Simple handler
        simple_handlers[sig]();
    }
}

void rt_signal_handler_install(int64_t signal, void (*handler)(void)) {
#ifdef _WIN32
    // Windows: Use SetConsoleCtrlHandler for SIGINT
    // (Not implemented for now)
    return;
#else
    // Unix/Linux/macOS
    if (signal >= 0 && signal < 32) {
        // Store Simple handler
        simple_handlers[signal] = handler;

        // Install C wrapper
        struct sigaction sa;
        sa.sa_handler = c_signal_handler;
        sigemptyset(&sa.sa_mask);
        sa.sa_flags = 0;

        sigaction((int)signal, &sa, NULL);
    }
#endif
}
```

---

### 3. rt_atexit_register()

**Signature:**
```c
void rt_atexit_register(void (*handler)(void));
```

**Purpose:** Register a cleanup function to run on normal exit

**Parameters:**
- `handler` - Simple function pointer to call on exit

**Implementation:**
```c
#include <stdlib.h>

// Global atexit handlers (max 32)
static void (*atexit_handlers[32])(void) = {NULL};
static int atexit_count = 0;

// C atexit handler
static void c_atexit_handler() {
    // Call handlers in reverse order (LIFO)
    for (int i = atexit_count - 1; i >= 0; i--) {
        if (atexit_handlers[i] != NULL) {
            atexit_handlers[i]();
        }
    }
}

void rt_atexit_register(void (*handler)(void)) {
    if (atexit_count == 0) {
        // Register C handler on first call
        atexit(c_atexit_handler);
    }

    if (atexit_count < 32) {
        atexit_handlers[atexit_count++] = handler;
    }
}
```

---

## Integration Points

### seed/runtime.c

Add these functions to the runtime library:

```c
// Signal handling functions
bool rt_signal_handler_available();
void rt_signal_handler_install(int64_t signal, void (*handler)(void));
void rt_atexit_register(void (*handler)(void));
```

### seed/runtime.h

Add declarations:

```c
// Signal handling
extern bool rt_signal_handler_available(void);
extern void rt_signal_handler_install(int64_t signal, void (*handler)(void));
extern void rt_atexit_register(void (*handler)(void));
```

---

## Usage Example

**Simple Code:**
```simple
use app.io.signal_handlers.{install_signal_handlers, SIGINT, SIGTERM}
use app.test_runner_new.runner_lifecycle.{cleanup_all_children}

fn my_cleanup():
    print "Cleaning up..."
    val cleaned = cleanup_all_children()
    print "Cleaned {cleaned} resources"

fn main():
    # Install signal handlers
    val installed = install_signal_handlers(my_cleanup)

    if installed:
        print "Signal handlers installed"
    else:
        print "WARNING: Signal handlers not available on this platform"

    # Run tests...
    run_tests()

    # Normal exit - my_cleanup() called automatically via atexit
```

**Behavior:**
```
User presses Ctrl+C during test run
  ↓
OS sends SIGINT (signal 2) to process
  ↓
Runtime calls c_signal_handler(2)
  ↓
c_signal_handler calls simple_handlers[2]
  ↓
simple_handlers[2] is on_sigint from signal_handlers.spl
  ↓
on_sigint calls _global_cleanup_handler
  ↓
_global_cleanup_handler is my_cleanup
  ↓
my_cleanup calls cleanup_all_children()
  ↓
Kills all tracked processes and containers
  ↓
Exits with code 130
```

---

## Thread Safety

**Considerations:**
- Signal handlers can interrupt execution at any time
- Need to ensure handlers are async-signal-safe
- Avoid malloc/free in signal handlers
- Keep handlers minimal (set flag, do cleanup in main loop)

**Alternative: Deferred Cleanup**
```c
// Global flag set by signal handler
static volatile sig_atomic_t shutdown_requested = 0;

static void c_signal_handler(int sig) {
    shutdown_requested = sig;
}

// In main loop (test_runner_main.spl)
fn main_loop():
    while tests_remaining:
        # Check shutdown flag
        if rt_shutdown_requested():
            perform_cleanup()
            exit(130)

        run_next_test()
```

---

## Testing

**Manual Test:**
```bash
# Compile test program
bin/simple build test_signal_handler.spl

# Run and press Ctrl+C
./test_signal_handler

# Expected output:
# Signal handlers installed
# Running tests...
# [User presses Ctrl+C]
# [SIGNAL] SIGINT received (Ctrl+C)
# [SIGNAL] Cleaning up resources...
# Cleaning up...
# Cleaned 3 resources
# [Exit code 130]
```

**Automated Test:**
```bash
# Start test runner
bin/simple test test/ &
PID=$!

# Wait 2 seconds
sleep 2

# Send SIGINT
kill -INT $PID

# Check exit code
wait $PID
EXIT_CODE=$?

# Should be 130
if [ $EXIT_CODE -eq 130 ]; then
    echo "PASS: Signal handler worked"
else
    echo "FAIL: Expected exit code 130, got $EXIT_CODE"
fi
```

---

## Fallback Behavior

**When SFFI not available:**
```simple
val installed = install_signal_handlers(my_cleanup)

if not installed:
    # Fallback: Use --self-protect mode instead
    # Resource monitoring will trigger graceful shutdown
    print "WARNING: Signal handlers not available"
    print "Using --self-protect mode for resource monitoring"
    options.self_protect = true
```

---

## Platform Support Matrix

| Platform | SIGHUP | SIGINT | SIGTERM | atexit() |
|----------|--------|--------|---------|----------|
| Linux | ✅ Yes | ✅ Yes | ✅ Yes | ✅ Yes |
| macOS | ✅ Yes | ✅ Yes | ✅ Yes | ✅ Yes |
| Windows | ❌ No | ⚠️ Limited | ❌ No | ✅ Yes |

**Windows Notes:**
- SIGINT can be handled via `SetConsoleCtrlHandler`
- SIGHUP and SIGTERM don't exist on Windows
- Use `atexit()` only for normal cleanup

---

## Security Considerations

**Signal Handler Safety:**
- Handlers should not call non-async-signal-safe functions
- Avoid: malloc, free, printf, file I/O
- Safe: set flags, simple arithmetic, exit()

**Race Conditions:**
- Multiple signals can arrive simultaneously
- Handlers can interrupt each other
- Use `sa_flags = SA_RESTART` to restart interrupted syscalls

**Denial of Service:**
- Rapid signal delivery can cause performance issues
- Consider rate-limiting cleanup attempts
- Set flag on first signal, ignore subsequent until cleanup complete

---

## Implementation Checklist

### Minimal (Phase 2A):
- [ ] Add `rt_signal_handler_available()` to seed/runtime.c
- [ ] Add `rt_signal_handler_install()` with basic sigaction
- [ ] Add `rt_atexit_register()` with stdlib atexit
- [ ] Test on Linux
- [ ] Test on macOS

### Full (Phase 2B):
- [ ] Thread safety (signal masking)
- [ ] Windows support (SetConsoleCtrlHandler for SIGINT)
- [ ] Signal handler chaining (preserve existing handlers)
- [ ] Deferred cleanup option (set flag instead of direct execution)
- [ ] Rate limiting for signal storms

---

## References

- POSIX Signal Handling: https://pubs.opengroup.org/onlinepubs/9699919799/functions/sigaction.html
- Linux Signal Man Page: `man 7 signal`
- Async-Signal-Safe Functions: https://man7.org/linux/man-pages/man7/signal-safety.7.html
- Windows Console Handlers: https://learn.microsoft.com/en-us/windows/console/setconsolectrlhandler
