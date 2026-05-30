# Duplication Reduction - Implementation Guide

**Date:** 2025-12-22  
**Status:** Helpers added, ready for refactoring

## Phase 1 Progress: Network FFI Helpers

### Completed

✅ **Helper macros added** to `src/runtime/src/value/net.rs`:
- `get_socket!()` - Access socket from registry with type checking
- `validate_buffer!()` - Validate FFI buffer parameters
- `parse_addr!()` - Parse socket address from FFI parameters
- `err_to_i64()`, `err_to_tuple2()`, `err_to_tuple3()` - Error conversion helpers

✅ **Compiles successfully** - No breaking changes

### Example Refactoring

**Before** (11 lines):
```rust
let registry = SOCKET_REGISTRY.lock().unwrap();
let entry = match registry.get(&handle) {
    Some(e) => e,
    None => return (0, NetError::InvalidHandle as i64),
};
let socket = match entry {
    SocketEntry::UdpSocket(s) => s,
    _ => return (0, NetError::InvalidHandle as i64),
};
```

**After** (1 line):
```rust
let socket = get_socket!(handle, UdpSocket, err_to_tuple2);
```

**Savings:** 10 lines per occurrence × ~45 occurrences = **~450 lines reduced**

### Files to Refactor

1. **src/runtime/src/value/net_udp.rs** (568 lines, 19 clones)
   - Functions: ~15 FFI functions
   - Pattern replacements: registry access (15×), buffer validation (8×), address parsing (10×)
   - Expected reduction: ~300 lines

2. **src/runtime/src/value/net_tcp.rs** (369 lines, 13 clones)
   - Functions: ~12 FFI functions
   - Pattern replacements: registry access (12×), buffer validation (6×), address parsing (8×)
   - Expected reduction: ~250 lines

3. **src/compiler/src/interpreter_native_net.rs** (803 lines, 13 clones)
   - Functions: ~20 interpreter bindings
   - Pattern replacements: similar patterns
   - Expected reduction: ~250 lines

### Implementation Steps

For each file:

1. **Find all registry access patterns:**
   ```bash
   grep -n "let registry = SOCKET_REGISTRY.lock" file.rs
   ```

2. **Replace with macro:**
   - Identify error return type (i64, (i64,i64), or (i64,i64,i64))
   - Use appropriate helper: `err_to_i64`, `err_to_tuple2`, or `err_to_tuple3`
   - Replace 8-11 line block with 1-line macro call

3. **Find buffer validations:**
   ```bash
   grep -n "if buf_ptr == 0 || buf_len" file.rs
   ```

4. **Replace with macro:**
   ```rust
   validate_buffer!(buf_ptr, buf_len, err_to_tuple2);
   ```

5. **Find address parsing:**
   ```bash
   grep -n "match parse_socket_addr" file.rs
   ```

6. **Replace with macro:**
   ```rust
   let addr = parse_addr!(addr_ptr, addr_len, err_to_tuple2);
   ```

7. **Test after each file:**
   ```bash
   cargo test -p simple-runtime
   ```

### Macro Usage Examples

**Example 1: UDP recv function**
```rust
// Before: 20 lines
pub unsafe extern "C" fn native_udp_recv(handle: i64, buf_ptr: i64, buf_len: i64) -> (i64, i64) {
    if buf_ptr == 0 || buf_len <= 0 {
        return (0, NetError::InvalidInput as i64);
    }
    
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return (0, NetError::InvalidHandle as i64),
    };
    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return (0, NetError::InvalidHandle as i64),
    };
    
    let buf = std::slice::from_raw_parts_mut(buf_ptr as *mut u8, buf_len as usize);
    match socket.recv(buf) {
        Ok(n) => (n as i64, NetError::Success as i64),
        Err(e) => (0, NetError::from(e) as i64),
    }
}

// After: 7 lines (saves 13 lines)
pub unsafe extern "C" fn native_udp_recv(handle: i64, buf_ptr: i64, buf_len: i64) -> (i64, i64) {
    validate_buffer!(buf_ptr, buf_len, err_to_tuple2);
    let socket = get_socket!(handle, UdpSocket, err_to_tuple2);
    let buf = std::slice::from_raw_parts_mut(buf_ptr as *mut u8, buf_len as usize);
    match socket.recv(buf) {
        Ok(n) => (n as i64, NetError::Success as i64),
        Err(e) => (0, NetError::from(e) as i64),
    }
}
```

**Example 2: UDP connect function**
```rust
// Before: 16 lines
pub unsafe extern "C" fn native_udp_connect(handle: i64, addr_ptr: i64, addr_len: i64) -> i64 {
    let addr = match parse_socket_addr(addr_ptr, addr_len) {
        Ok(a) => a,
        Err(e) => return e as i64,
    };
    
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };
    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };
    
    match socket.connect(addr) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

// After: 5 lines (saves 11 lines)
pub unsafe extern "C" fn native_udp_connect(handle: i64, addr_ptr: i64, addr_len: i64) -> i64 {
    let addr = parse_addr!(addr_ptr, addr_len, err_to_i64);
    let socket = get_socket!(handle, UdpSocket, err_to_i64);
    match socket.connect(addr) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}
```

## Expected Results

After refactoring these 3 files:

| Metric | Before | After | Reduction |
|--------|--------|-------|-----------|
| Lines | 1740 | ~940 | -800 lines |
| Clones | 45 | ~10 | -35 clones |
| Duplication % | 4.49% | ~3.8% | -0.69% |

## Next Steps

1. Apply macros to net_udp.rs (highest impact)
2. Apply macros to net_tcp.rs
3. Apply macros to interpreter_native_net.rs
4. Run tests: `cargo test -p simple-runtime`
5. Measure duplication: `jscpd ./src --min-lines 5 --min-tokens 50`
6. Proceed to Phase 2 if duplication is still above 2.5%

## Verification

After completing Phase 1:

```bash
# Check duplication
jscpd ./src --min-lines 5 --min-tokens 50 --reporters "console"

# Run tests
cargo test --workspace

# Should see:
# - Duplication reduced to ~3.8%
# - All tests passing
# - No compilation warnings
```

## Implementation Update (2025-12-22 10:05)

### Issue Discovered: Macro Lifetime Constraints

The `get_socket!()` macro has a borrow checker limitation:

**Problem:**
```rust
macro_rules! get_socket {
    ($handle:expr, $variant:ident, $error_ret:expr) => {{
        let registry = SOCKET_REGISTRY.lock().unwrap();  // Lock guard created
        let entry = registry.get(&$handle);               // Borrow from guard
        // Guard dropped here, but entry tries to outlive it
    }};
}
```

The returned socket reference borrows from `registry`, which is dropped at macro end.

### Alternative Approach: Inline Pattern

Instead of extracting to a macro, use **consistent inline patterns** with clear naming:

**Standard Pattern for Registry Access:**
```rust
pub unsafe extern "C" fn native_udp_operation(handle: i64, ...) -> ReturnType {
    // 1. Validate inputs if needed
    validate_buffer!(buf_ptr, buf_len, err_fn);  // OK - no lifetime issues
    
    // 2. Access registry - keep guard in scope
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let socket = match registry.get(&handle)
        .and_then(|e| if let SocketEntry::UdpSocket(s) = e { Some(s) } else { None })
    {
        Some(s) => s,
        None => return err_to_tuple2(NetError::InvalidHandle),
    };
    
    // 3. Perform operation - registry guard still alive
    let result = socket.operation(...);
    
    // 4. Return - registry guard dropped here
    match result {
        Ok(val) => (val as i64, NetError::Success as i64),
        Err(e) => (0, NetError::from(e) as i64),
    }
}
```

This reduces from 11 lines to 5 lines while avoiding lifetime issues.

### Revised Reduction Strategy

**Keep the helper functions:** `validate_buffer!()`, `parse_addr!()`, error conversions  
**Use inline patterns for:** Registry access (lifetime constraints prevent macro extraction)

**Expected Savings:**
- Buffer validation: 3 lines → 1 line (2 lines × 10 uses = -20 lines)
- Address parsing: 5 lines → 1 line (4 lines × 15 uses = -60 lines)  
- Registry access: Improved readability, minimal line reduction
- **Total Phase 1:** ~80-100 lines reduction (not 800 as initially estimated)

### Recommendation

For significant duplication reduction (reaching <2.5%):
1. Apply `validate_buffer!()` and `parse_addr!()` macros (~80 lines)
2. **Focus on Phase 2 & 3** (interpreter helpers, test helpers) for bigger wins
3. Consider **test helper consolidation** as highest-impact area
4. Save networking refactoring for when larger architectural changes are made

The test code duplications (Phase 3) offer better ROI - test helper functions don't have the same lifetime constraints as FFI code.
