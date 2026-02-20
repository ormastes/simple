# Debug Skill - Simple Compiler Debugging

## Logging Setup

### Enable Tracing
```bash
# Set log level
SIMPLE_LOG=debug bin/simple file.spl

# Specific module
SIMPLE_LOG=interpreter=trace bin/simple file.spl
```

### GC Logging
```bash
# Enable GC debug output
bin/simple --gc-log file.spl
```

## Interpreter Debugging

### Interpreter Modules
```
src/app/interpreter/
├── core.spl      # Main entry point
├── call.spl      # Function calls
├── module.spl    # Module loading
└── expr.spl      # Expression evaluation
```

### Add Debug Tracing
```simple
# Add print-based debugging in Simple code
fn interpret_expr(expr):
    print "DEBUG: interpreting expression: {expr}"
    val result = evaluate(expr)
    print "DEBUG: result = {result}"
    result
```

## Codegen Debugging

### IR Export
```bash
# Export AST
bin/simple --emit-ast=ast.json file.spl

# Export HIR (type-checked)
bin/simple --emit-hir=hir.json file.spl

# Export MIR (lowered)
bin/simple --emit-mir=mir.json file.spl

# All to stdout
bin/simple --emit-ast --emit-hir --emit-mir file.spl
```

### Compilability Analysis
Check why code falls back to interpreter:
```bash
# In logs, look for:
# "Falling back to interpreter: <reason>"
# 20+ fallback reasons tracked
SIMPLE_LOG=debug bin/simple --compile file.spl
```

### Cranelift Debug
```bash
# Enable Cranelift IR dumps
CRANELIFT_DEBUG=1 bin/simple --compile file.spl
```

## Runtime Debugging

### RuntimeValue Structure
```
64-bit tagged pointer:
┌──────────────────────────────────────────────────────┐
│ Payload (48-62 bits)              │ Tag (2-16 bits)  │
└──────────────────────────────────────────────────────┘

Tags:
- 0b00: Pointer (heap object)
- 0b01: Small integer
- 0b10: Special (nil, true, false)
- 0b11: Symbol
```

## Test Debugging

### Run Single Test
```bash
# Run with verbose output
bin/simple --verbose src/lib/test/unit/core/test_spec.spl

# Step through (if DAP available)
bin/simple --debug src/lib/test/unit/core/test_spec.spl
```

## Fault Detection

### Stack Overflow Detection
```bash
# Enabled by default in debug builds, disabled in release
SIMPLE_STACK_OVERFLOW_DETECTION=1 bin/simple file.spl

# Set custom recursion depth limit (default: 1000)
SIMPLE_MAX_RECURSION_DEPTH=500 bin/simple file.spl
```
- Implemented with AtomicUsize + RAII guard
- ~2 atomic ops per function call (Relaxed ordering)
- Error: `StackOverflow { depth, limit, function_name }`

### Timeout Detection (Wall-Clock)
```bash
# Set execution timeout in seconds (0 = disabled, default)
SIMPLE_TIMEOUT_SECONDS=30 bin/simple file.spl

# Short timeout for testing infinite loops
SIMPLE_TIMEOUT_SECONDS=1 bin/simple loop_test.spl
```
- Watchdog thread checks every 100ms
- Zero overhead on fast path (single AtomicBool load, Relaxed)
- Checked at loop back-edges alongside `check_interrupt!()` and `check_execution_limit!()`

### Crash Detection
- Runtime wraps execution to catch crashes
- Crashes produce: `fatal: interpreter crashed: <message>` (exit code 101)
- Backtrace logged to stderr

### Memory Leak Detection
```bash
# Enable heap growth heuristic (opt-in)
SIMPLE_LEAK_DETECTION=1 bin/simple file.spl
```
- Tracks post-GC heap size over 10 cycles
- Warns if heap grows >10% over window
- Zero overhead when disabled; runs only in GC collection path

### Execution Limit (existing)
```bash
# Set instruction count limit (default: 10M, 0 = disabled)
SIMPLE_EXECUTION_LIMIT=1000000 bin/simple file.spl
SIMPLE_EXECUTION_LIMIT_ENABLED=false bin/simple file.spl
```

### Env Var Summary
| Variable | Default | Purpose |
|---|---|---|
| `SIMPLE_STACK_OVERFLOW_DETECTION` | debug=on, release=off | Recursion depth check |
| `SIMPLE_MAX_RECURSION_DEPTH` | 1000 | Max call depth |
| `SIMPLE_TIMEOUT_SECONDS` | 0 (off) | Wall-clock timeout |
| `SIMPLE_EXECUTION_LIMIT` | 10000000 | Instruction count limit |
| `SIMPLE_EXECUTION_LIMIT_ENABLED` | debug=on, release=off | Enable instruction limit |
| `SIMPLE_LEAK_DETECTION` | false | Heap growth heuristic |

## Common Issues

### "Falling back to interpreter"
- Usually: unsupported MIR instruction, complex pattern, dynamic dispatch
- Check logs with `SIMPLE_LOG=debug` for specific fallback reason

### Memory Issues
- Enable GC logging: `--gc-log`
- Enable leak detection: `SIMPLE_LEAK_DETECTION=1`

### Type Errors
- Export HIR: `--emit-hir` to see inferred types

### Pattern Match Failures
- PatternTest/PatternBind MIR instructions
- Check exhaustiveness with `--emit-mir`

## Useful Debug Patterns

### Conditional Debug Output (in tests)
```simple
# Add conditional debug output
if env_get("DEBUG_TEST") != "":
    print "Debug info..."
```

## MCP-Based Debugging (NEW)

### Start MCP Server
```bash
# Start MCP server for interactive debugging
bin/simple src/app/mcp/main.spl server --debug

# CLI mode - read/analyze files
bin/simple src/app/mcp/main.spl read src/compiler/driver.spl
bin/simple src/app/mcp/main.spl json src/compiler/driver.spl
```

### MCP Tools Available
- `read_code <file>` - Read Simple source files with syntax highlighting
- `list_files <dir>` - List .spl files in directory
- `search_code <query>` - Search for code patterns
- `file_info <file>` - Get file statistics (lines, functions, classes)

### Bootstrap Debugging
```bash
# Run bootstrap with debug capture
scripts/capture_bootstrap_debug.sh

# Run specific stage
scripts/bootstrap.sh --stage=1
scripts/bootstrap.sh --stage=2

# Verify determinism
scripts/bootstrap.sh --verify

# Extended multi-generation test
bin/simple scripts/bootstrap_extended.spl --generations=5
```

### Debug Instrumentation Points

**Phase 3 (HIR Lowering):**
```
[phase3] parsed modules count=N
[phase3] DEBUG: module_names = [...]
[phase3] stored HIR module 'X', total now: N
[phase3] loop complete. HIR modules keys: [...]
[phase3] returning ctx with N HIR modules
```

**Phase 5 (AOT Compilation):**
```
[aot] DEBUG: ctx.hir_modules count = N
[aot] lowering to MIR...
[aot] MIR done, N modules
```

### Common Bootstrap Issues

**Issue: "MIR done, 0 modules"**
- HIR modules created in phase 3 but lost before phase 5
- Check context flow: `[compile] BEFORE/AFTER phase 3`
- Verify: `ctx.hir_modules.keys().len()` at each phase

**Issue: "No object files to link"**
- MIR lowering found 0 HIR modules to process
- Root cause: Context not preserved between phases
- Debug: Add prints in `lower_and_check_impl()` return

**Issue: Bootstrap timeout (>60s)**
- Large debug output slowing compilation
- Use `SIMPLE_LOG=warn` to reduce verbosity
- Profile with: `time scripts/bootstrap.sh --stage=1`

### Automated Bug Detection

**Test Dictionary Semantics:**
```bash
bin/simple scripts/test_dict_semantics.spl
# Should show: "ALL TESTS PASSED"
```

**MCP Debug Script:**
```bash
bin/simple scripts/mcp_debug_bootstrap.spl
# Auto-detects common bug patterns
```

### Bug Database

**View registered bugs:**
```bash
cat doc/bug/bug_db.sdn
# SDN format: bugs, test_cases, fixes, notes
```

**Bug Analysis Reports:**
- `doc/bug/mcp_bug_analysis_2026-01-29.md` - MCP analysis
- `doc/bug/bootstrap_mir_zero_modules.md` - Bootstrap bug details
- `doc/report/bootstrap_investigation_2026-01-29.md` - Investigation log

### Live Debugging Workflow

1. **Capture Debug Output:**
   ```bash
   scripts/capture_bootstrap_debug.sh
   # Saves to: build/bootstrap_debug_TIMESTAMP.log
   ```

2. **Extract Key Messages:**
   ```bash
   grep -E "\[phase3\]|\[aot\]" build/bootstrap_debug_*.log
   ```

3. **Identify Loss Point:**
   - Compare HIR module count at phase 3 exit vs phase 5 entry
   - If phase 3 shows N but phase 5 shows 0, modules lost between

4. **Register Bug:**
   ```bash
   # Add to doc/bug/bug_db.sdn
   bugs |id, severity, status, title, file, line, description|
       bug_id, P0, confirmed, "Description", "file.spl", 123, "Details", "test_case"
   ```

5. **Apply Fix & Test:**
   ```bash
   # After fixing
   bin/simple build
   scripts/bootstrap.sh --verify
   ```

## See Also

- `doc/codegen_technical.md` - Codegen details
- `doc/bug/bug_db.sdn` - Bug tracking database
- `src/app/mcp/` - MCP server and debugging tools
- `src/app/interpreter/` - Interpreter modules
- `src/compiler/` - Compiler source (Pure Simple)
