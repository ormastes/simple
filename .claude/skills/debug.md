# Debug Skill

## Logging & Tracing

```bash
SIMPLE_LOG=debug bin/simple file.spl                # Set log level
SIMPLE_LOG=interpreter=trace bin/simple file.spl    # Module-specific
bin/simple --gc-log file.spl                        # GC debug output
```

## IR Export

```bash
bin/simple --emit-ast=ast.json file.spl    # AST
bin/simple --emit-hir=hir.json file.spl    # HIR (type-checked)
bin/simple --emit-mir=mir.json file.spl    # MIR (lowered)
CRANELIFT_DEBUG=1 bin/simple --compile file.spl  # Cranelift IR dumps
```

## Diagnostics via Query Engine

```bash
bin/simple query check <file> --format json          # Type-check + lint
bin/simple query workspace-diagnostics <dir>         # Workspace-wide
bin/simple query hover <file> <line>                 # Type + docs at position
```

## Fault Detection Env Vars

| Variable | Default | Purpose |
|----------|---------|---------|
| `SIMPLE_STACK_OVERFLOW_DETECTION` | debug=on, release=off | Recursion depth check |
| `SIMPLE_MAX_RECURSION_DEPTH` | 1000 | Max call depth |
| `SIMPLE_TIMEOUT_SECONDS` | 0 (off) | Wall-clock timeout |
| `SIMPLE_EXECUTION_LIMIT` | 10000000 | Instruction count limit |
| `SIMPLE_LEAK_DETECTION` | false | Heap growth heuristic |

## Common Issues

| Symptom | Debug Step |
|---------|-----------|
| "Falling back to interpreter" | `SIMPLE_LOG=debug` for fallback reason |
| Memory issues | `--gc-log` + `SIMPLE_LEAK_DETECTION=1` |
| Type errors | `--emit-hir` to see inferred types |
| Pattern match failures | `--emit-mir` for PatternTest/PatternBind |

## RuntimeValue Tags

```
0b00: Pointer (heap)  |  0b01: Small integer
0b10: Special (nil/bool)  |  0b11: Symbol
```

## Bootstrap Debugging

```bash
scripts/capture_bootstrap_debug.sh     # Capture debug output
scripts/bootstrap.sh --stage=1         # Run specific stage
scripts/bootstrap.sh --verify          # Verify determinism
```

Key instrumentation: `[phase3]` (HIR lowering), `[aot]` (compilation)

## Live Debugging Workflow

1. **Capture**: `scripts/capture_bootstrap_debug.sh`
2. **Analyze**: Check HIR module count at phase 3 exit vs phase 5 entry
3. **Register bug**: `doc/tracking/bug/bug_db.sdn`
4. **Fix & verify**: `bin/simple build && scripts/bootstrap.sh --verify`

## See Also

- `/debug-lsp` skill for DAP+LSP chaining
- `doc/tracking/bug/bug_db.sdn` - Bug database
- `src/compiler/` - Compiler source
