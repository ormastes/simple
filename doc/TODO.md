# TODO List

**Generated:** 2026-05-30
**Total:** 4 items | **Open:** 4 | **Blocked:** 0 | **Stale:** 0
**Database:** `doc/todo/todo_db.sdn`

## Statistics

### By Area

| Area | Count | P0 | P1 | P2 | P3 | Blocked |
|------|-------|----|----|----|----|---------|
| runtime | 2 | 0 | 1 | 1 | 0 | 0 |
| stdlib | 1 | 0 | 0 | 1 | 0 | 0 |
| ui | 1 | 0 | 0 | 1 | 0 | 0 |

### By Priority

| Priority | Count | Open | Blocked | Stale |
|----------|-------|------|---------|-------|
| P0 (critical) | 0 | 0 | 0 | 0 |
| P1 (high) | 1 | 1 | 0 | 0 |
| P2 (medium) | 3 | 3 | 0 | 0 |
| P3 (low) | 0 | 0 | 0 | 0 |

## P1 High Priority TODOs

### runtime

- **#1** [runtime][P1] A real GPU framebuffer readback is not available under
  - File: `./src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:229`
  - Status: open


## P2 Medium Priority TODOs (3)

### runtime

- **#2** [runtime][P2] Interpreter loses the `self` binding when a struct
  - File: `./src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:262`
  - Status: open

### stdlib

- **#3** [stdlib][P2] extract ALPN from handshake state when ALPN is implemented
  - File: `./src/lib/nogc_async_mut/http_server/worker.spl:346`
  - Status: open

### ui

- **#0** [ui][P2] This is a substring-heuristic rasterizer, not a real HTML
  - File: `./src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl:469`
  - Status: open


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
