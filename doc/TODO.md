# TODO List

**Generated:** 2026-04-16
**Total:** 4 items | **Open:** 4 | **Blocked:** 0 | **Stale:** 0
**Database:** `doc/todo/todo_db.sdn`

## Statistics

### By Area

| Area | Count | P0 | P1 | P2 | P3 | Blocked |
|------|-------|----|----|----|----|---------|
| runtime | 2 | 0 | 1 | 0 | 1 | 0 |
| test | 2 | 0 | 2 | 0 | 0 | 0 |

### By Priority

| Priority | Count | Open | Blocked | Stale |
|----------|-------|------|---------|-------|
| P0 (critical) | 0 | 0 | 0 | 0 |
| P1 (high) | 3 | 3 | 0 | 0 |
| P2 (medium) | 0 | 0 | 0 | 0 |
| P3 (low) | 1 | 1 | 0 | 0 |

## P1 High Priority TODOs

### test

- **#60** [test][P1] build the real compiled WSS e2e driver — _ws_client.spl + socket round trip
  - File: `./tests/app/ui.web/live_smoke_test.spl:1`
  - Status: open

- **#61** [test][P1] add `bin/simple test --compile` so sspec `it` blocks actually execute
  - File: `./tests/app/ui.web/live_smoke_test.spl:2`
  - Status: open


## P3 Low Priority TODOs (1)

*See database for details.*

## Appendix

### Legend

- **P0/critical:** Blocking, fix immediately
- **P1/high:** Important, next sprint
- **P2/medium:** Should do, backlog
- **P3/low:** Nice to have, someday

### Areas

- `runtime` - GC, values, monoio, concurrency
- `codegen` - MIR, Cranelift, LLVM, Vulkan
- `compiler` - HIR, pipeline, interpreter
- `parser` - Lexer, AST, parsing
- `type` - Type checker, inference
- `stdlib` - Simple standard library
- `gpu` - GPU/SIMD/graphics
- `ui` - UI framework
- `test` - Test frameworks
- `driver` - CLI, tools
- `loader` - SMF loader
- `pkg` - Package manager
- `doc` - Documentation, specs, guides
