# Runtime Debug Logging Fix - 2026-02-14

## Issue

MCP server fails to start because runtime outputs massive debug spam:
- ~60,000 lines of `[DEBUG] register_definitions: processing node type: Discriminant(N)`
- Output floods stderr during module loading
- Server times out before reaching `start_server()` function
- `RUST_LOG=error` environment variable is **IGNORED**

## Root Cause

1. **Hardcoded debug output:** Runtime uses `println!`/`eprintln!` instead of `log` crate
2. **Debug builds in production:** `bin/release/simple` has `with debug_info, not stripped`
3. **No conditional compilation:** Debug output always enabled, can't be disabled

## Requirements for Next Release

### 1. Use `log` Crate Properly

Replace hardcoded debug output:
```rust
// BAD (current)
eprintln!("[DEBUG] register_definitions: processing {} items", count);

// GOOD (desired)
debug!("register_definitions: processing {} items", count);
```

### 2. Default Behavior

- **Release builds:** Debug logging OFF by default
- **Debug builds:** Debug logging ON by default
- **All builds:** Respect `RUST_LOG` environment variable

### 3. Build Process

Ensure release binaries are properly stripped:
```bash
cargo build --release
strip target/release/simple
```

### 4. Testing

Verify fix works:
```bash
# Should produce NO debug output
RUST_LOG=error bin/release/simple src/app/mcp/main.spl server

# Should produce debug output when requested
RUST_LOG=debug bin/release/simple src/app/mcp/main.spl server
```

## Current Workarounds

1. **MCP wrapper scripts:** Use `2>/dev/null` to suppress stderr (already implemented)
2. **Longer timeouts:** Server eventually starts after ~10-30 seconds of debug spam
3. **Patience:** Wait for module loading to complete

## Impact

- ✅ `.mcp.json` already has `RUST_LOG: "error"` (correct)
- ✅ Wrapper scripts already use `2>/dev/null` (working)
- ❌ Server still times out in testing (needs proper fix)
- ❌ Cannot debug MCP server issues (stderr suppressed)

## Status

**For next release:** Runtime rebuild with proper logging controls required.

**Current state:** Workarounds allow MCP server to function in production (Claude Desktop) but make local testing difficult.
