# Phase 4: MCP Protocol Library Consolidation

**Date:** 2026-02-16
**Status:** ✅ COMPLETE
**Test Results:** 475/475 passing (100%)

## Summary

Extracted common MCP protocol I/O functions into a shared library module (`src/mcp_lib/protocol.spl`) to eliminate duplication across 7 MCP server implementations.

## Consolidation Results

### Created Files
- **`src/mcp_lib/protocol.spl`** (79 lines)
  - Protocol state management (JSON Lines vs Content-Length auto-detection)
  - `protocol_read_message()` - stdin parsing with both protocol modes
  - `protocol_write_message()` - stdout writing with appropriate framing
  - `create_protocol_state()` - factory for protocol state
  - `ProtocolState` class - tracks detected protocol mode

### Modified Files

#### Non-Lite Servers (Updated)
1. **`src/app/mcp/main.spl`**
   - Added import: `use mcp_lib.protocol.{...}`
   - Replaced `var USE_JSON_LINES = false` with `var PROTOCOL = create_protocol_state()`
   - Converted `read_stdin_message()` and `write_stdout_message()` to thin delegation
   - Lines saved: ~20 lines

2. **`src/app/mcp/fileio_main.spl`**
   - Same pattern as main.spl
   - Lines saved: ~28 lines

3. **`src/app/mcp_jj/main.spl`**
   - Same pattern as main.spl
   - Lines saved: ~20 lines

#### Library Module
4. **`src/mcp_lib/mod.spl`**
   - Added protocol module exports
   - Updated documentation to include protocol I/O

#### Unchanged (Zero-Import Constraint)
- `src/app/mcp/main_lite.spl` - KEPT inlined (zero-import startup)
- `src/app/mcp/fileio_lite.spl` - KEPT inlined (zero-import startup)
- `src/app/mcp_jj/main_lite.spl` - KEPT inlined (zero-import startup)
- `src/app/mcp/main_lazy.spl` - KEPT inlined (fast startup ~100ms constraint)

## Lines Eliminated

| File | Before | After | Saved |
|------|--------|-------|-------|
| main.spl | 22 lines protocol | 2 lines delegation | 20 |
| fileio_main.spl | 30 lines protocol | 2 lines delegation | 28 |
| mcp_jj/main.spl | 22 lines protocol | 2 lines delegation | 20 |
| **Total** | | | **~68 lines** |

**Protocol module created:** 79 lines
**Net change:** +79 - 68 = **+11 lines** (acceptable for abstraction)

## Technical Details

### Protocol Auto-Detection
The protocol module automatically detects which framing mode the client uses:
- **JSON Lines mode:** When first message starts with `{`
- **Content-Length mode:** When first message starts with `Content-Length:`

Once detected, all subsequent messages use the same mode.

### Protocol State
```simple
class ProtocolState:
    use_json_lines: bool
```

Tracks the detected mode across message reads/writes.

### API
```simple
use mcp_lib.protocol.{create_protocol_state, protocol_read_message, protocol_write_message}

var PROTOCOL = create_protocol_state()
val msg = protocol_read_message(PROTOCOL)  # Returns text or "" on EOF
protocol_write_message(PROTOCOL, response)  # Writes with appropriate framing
```

## Build Verification

All three updated servers compile successfully:
```bash
bin/simple build src/app/mcp/main.spl --check          # ✅ Build succeeded
bin/simple build src/app/mcp/fileio_main.spl --check   # ✅ Build succeeded
bin/simple build src/app/mcp_jj/main.spl --check       # ✅ Build succeeded
```

## Test Results

### Lib Tests (121 tests)
```
Running 121 test file(s) [mode: interpreter]...
=========================================
Results: 121 total, 121 passed, 0 failed
Time:    450ms
=========================================
All tests passed!
```

### App Tests (354 tests)
```
Running 354 test file(s) [mode: interpreter]...
=========================================
Results: 354 total, 354 passed, 0 failed
Time:    1261ms
=========================================
All tests passed!
```

**Combined: 475/475 tests passing (100%)**

## Design Rationale

### Why Not Consolidate _lite Files?
The `*_lite.spl` files are explicitly designed for zero-import fast startup. They serve as minimal MCP servers that:
- Start in <50ms
- Have no dependencies beyond core language features
- Provide essential tooling for embedded/constrained environments

Adding imports would defeat their purpose.

### Why Not Consolidate main_lazy.spl?
`main_lazy.spl` has a "zero-import startup" constraint for fast startup (~100ms with lazy handler loading). It trades duplication for startup performance.

## Patterns Established

### Thin Delegation Pattern
```simple
fn read_stdin_message() -> text:
    """Read message using MCP protocol (delegates to protocol module)."""
    protocol_read_message(PROTOCOL)

fn write_stdout_message(body: text):
    """Write message using MCP protocol (delegates to protocol module)."""
    protocol_write_message(PROTOCOL, body)
```

This preserves the existing API while consolidating implementation.

## Benefits

1. **Single Source of Truth:** Protocol handling logic now in one place
2. **Easier Maintenance:** Bug fixes apply to all servers automatically
3. **Consistent Behavior:** All servers use identical protocol handling
4. **Better Testing:** Protocol logic can be unit-tested independently
5. **Future-Proof:** New protocol features only need one implementation

## Integration with Existing Code

The consolidation maintains full backward compatibility:
- Existing MCP tool handlers work unchanged
- Server initialization logic unchanged
- Tool dispatch logic unchanged
- Only protocol I/O layer was extracted

## Future Work

Potential Phase 5 candidates (not in original plan):
- Extract common `make_initialize_response()` logic (server-specific currently)
- Consolidate handler dispatch patterns (varies by server architecture)
- Extract common resource/prompt handling patterns

## Related Documentation

- Phase 1-3 Completion: `doc/report/*_deduplication_*_2026-02-16.md`
- Original Plan: `.claude/plans/calm-nibbling-octopus.md`
- MCP Library: `src/mcp_lib/mod.spl`
- Protocol Module: `src/mcp_lib/protocol.spl`

## Conclusion

Phase 4 successfully consolidates MCP protocol I/O across 3 production servers while respecting zero-import constraints for lite/lazy variants. All 475 tests pass with zero regressions.

**Semantic Deduplication: 100% COMPLETE (Phases 1-4)**
