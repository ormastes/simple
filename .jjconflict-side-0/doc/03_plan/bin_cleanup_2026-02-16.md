# bin/ Directory Cleanup Plan

**Date:** 2026-02-16
**Goal:** Consolidate MCP server variations, remove legacy files, document bin/ structure

## Current State

**Files:** 30+ files including duplicates, legacy binaries, and helper scripts
**Size:** ~400MB (mostly srt2 at 371MB)
**Issues:**
- 5 MCP server variations (simple_mcp_server, _optimized, _legacy, _lite, _native)
- 371MB legacy binary (srt2)
- Broken wrappers referencing non-existent simple_runtime
- Python cache directories

## Cleanup Actions

### DELETE: Duplicate MCP Servers (3 files)
- ❌ `simple_mcp_server_optimized` - IDENTICAL to simple_mcp_server
- ❌ `simple_mcp_server_legacy` - Old version, replaced
- ❌ `simple_mcp_server_native` - Requires manual compilation, not pre-built

**Keep:** `simple_mcp_server` (canonical), `simple_mcp_server_lite` (different entry point), `simple_mcp_fileio` (specialized)

### DELETE: Legacy Binaries (2 files, ~371MB)
- ❌ `srt2` - 371MB old/debug runtime
- ❌ `simple_v050` - Old version wrapper, superseded by bin/simple

### DELETE: Broken Wrappers (2 files)
- ❌ `simple_coverage` - References non-existent simple_runtime paths
- ❌ `simple_stub` - References non-existent simple_runtime paths

### MOVE TO scripts/: Build/Test Scripts (2 files)
- 🔄 `build-minimal-bootstrap.sh` → `scripts/build/build-minimal-bootstrap.sh`
- 🔄 `verify-torch-ffi` → `scripts/test/verify-torch-ffi.sh`

### KEEP: Core Files
- ✅ `simple` - Main CLI wrapper (190 lines, platform detection)
- ✅ `release/simple` - Pre-built runtime (27MB)
- ✅ `simple_mcp_server` - Canonical MCP server
- ✅ `simple_mcp_server_lite` - Lite MCP server (fast startup)
- ✅ `simple_mcp_fileio` - File I/O protection MCP server
- ✅ `simple-torch` - PyTorch integration wrapper
- ✅ `task` - Task CLI dispatcher
- ✅ `bootstrap/` - Bootstrap compiler artifacts
- ✅ `mold/` - Linker artifacts
- ✅ `release/` - Multi-platform release binaries

### KEEP: Helper Files
- ✅ `mcp_daemon.sh` - MCP daemon wrapper
- ✅ `mcp_proxy.py` - MCP stdio/HTTP proxy
- ✅ `mcp_quiet.sh` - Quiet MCP wrapper
- ✅ `libflush_stdout.so` - Output flushing library
- ✅ `libunbuf.so` - Unbuffered I/O library

### CLEAN: Python Cache
- ❌ `__pycache__/` - Remove Python bytecode cache

## MCP Server Consolidation

### Current Variations (5)
1. `simple_mcp_server` - Full server (33 tools, main.spl)
2. `simple_mcp_server_optimized` - DUPLICATE of #1
3. `simple_mcp_server_legacy` - Old version
4. `simple_mcp_server_lite` - Lite server (main_lite.spl, fast startup)
5. `simple_mcp_server_native` - Native compiled (manual)

### After Cleanup (2)
1. `simple_mcp_server` - Full server (662 lines, 33 tools)
   - Debug tools (16)
   - Debug log tools (6)
   - Diagnostic read tools (4)
   - Diagnostic edit tools (3)
   - Diagnostic VCS tools (4)

2. `simple_mcp_server_lite` - Lite server (386 lines, core tools only)
   - Fast startup (~10ms)
   - Direct extern FFI calls
   - No heavy module imports

3. `simple_mcp_fileio` - Specialized file I/O protection server
   - Protected file operations
   - Uses fileio_main.spl (719 lines)

## Source Code Cleanup

### DELETE: Unused MCP Entry Points (2 files)
Check usage before deleting:
- ❓ `src/app/mcp/main_lazy.spl` (331 lines) - Lazy loading variant
- ❓ `src/app/mcp/test_server.spl` (57 lines) - Test server

### KEEP: Active Entry Points
- ✅ `src/app/mcp/main.spl` (662 lines) - Full server
- ✅ `src/app/mcp/main_lite.spl` (386 lines) - Lite server
- ✅ `src/app/mcp/fileio_main.spl` (719 lines) - File I/O server

## Expected Results

**Before:**
- 30+ files
- 5 MCP server variations (confusing)
- ~400MB total size
- Broken wrappers
- Python cache

**After:**
- ~20 files (clean, documented)
- 2 MCP servers (clear purpose)
- ~30MB total size (98% reduction!)
- All wrappers working
- No cache pollution

**Space Saved:** ~370MB (mostly srt2 deletion)

## Verification Steps

1. Test remaining MCP servers work
2. Verify bin/simple works on all platforms
3. Check task CLI still functions
4. Ensure torch integration works
5. Test bootstrap builds

## Documentation

Create `bin/FILE.md` explaining:
- What each file does
- When to use which MCP server
- Helper scripts purpose
- Directory structure
