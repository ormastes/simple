# TODO List

**Generated:** 2026-01-19
**Total:** 45 items | **Open:** 45 | **Blocked:** 0 | **Stale:** 0
**Database:** `doc/todo/todo_db.sdn`

## Statistics

### By Area

| Area | Count | P0 | P1 | P2 | P3 | Blocked |
|------|-------|----|----|----|----|---------|
| doc | 10 | 1 | 8 | 1 | 0 | 0 |
| gpu | 2 | 1 | 1 | 0 | 0 | 0 |
| parser | 1 | 0 | 0 | 1 | 0 | 0 |
| runtime | 5 | 3 | 0 | 2 | 0 | 0 |
| stdlib | 24 | 3 | 0 | 1 | 20 | 0 |
| test | 2 | 0 | 0 | 0 | 2 | 0 |
| ui | 1 | 0 | 0 | 1 | 0 | 0 |

### By Priority

| Priority | Count | Open | Blocked | Stale |
|----------|-------|------|---------|-------|
| P0 (critical) | 8 | 8 | 0 | 0 |
| P1 (high) | 9 | 9 | 0 | 0 |
| P2 (medium) | 6 | 6 | 0 | 0 |
| P3 (low) | 22 | 22 | 0 | 0 |

## P0 Critical TODOs

### doc

- **#46** [doc][P0] Fix broken links [#567] [blocked:123]
  - File: `claude/skills/todo.md:54`
  - Status: open
  - Blocked by: 123

### gpu

- **#85** [gpu][P0] Fix render pipeline memory leak [#567]
  - File: `test_todo_sample.spl:3`
  - Status: open

### runtime

- **#75** [runtime][P0] Implement monoio TCP write [#234]
  - File: `src/driver/src/todo_parser.rs:483`
  - Status: open

- **#77** [runtime][P0] Real TODO
  - File: `src/driver/src/todo_parser.rs:587`
  - Status: open

- **#79** [runtime][P0] Implement monoio TCP write [#234]
  - File: `test_todo_sample.rs:2`
  - Status: open

### stdlib

- **#76** [stdlib][P0] Fix memory leak [#567] [blocked:123]
  - File: `src/driver/src/todo_parser.rs:485`
  - Status: open
  - Blocked by: 123

- **#80** [stdlib][P0] Fix memory leak [#567] [blocked:123]
  - File: `test_todo_sample.rs:3`
  - Status: open
  - Blocked by: 123

- **#84** [stdlib][P0] Implement socket write via FFI [#234]
  - File: `test_todo_sample.spl:2`
  - Status: open


## P1 High Priority TODOs

### doc

- **#45** [doc][P1] Add examples section [#234]
  - File: `claude/skills/todo.md:53`
  - Status: open

- **#47** [doc][P1] Add examples section [#234]
  - File: `doc/design/IMPLEMENTATION_SUMMARY.md:121`
  - Status: open

- **#48** [doc][P1] Add architecture diagram [#123]
  - File: `doc/design/TODO_CONTRIBUTING_UPDATE.md:95`
  - Status: open

- **#50** [doc][P1] Add architecture diagram [#123]
  - File: `doc/design/TODO_QUICKSTART.md:261`
  - Status: open

- **#51** [doc][P1] Add examples section [#234]
  - File: `doc/design/TODO_SYSTEM_COMPLETE.md:132`
  - Status: open

- **#52** [doc][P1] Add examples section [#234]
  - File: `doc/design/dual_language_parsing_summary.md:53`
  - Status: open

- **#53** [doc][P1] Add examples section [#234]
  - File: `doc/design/dual_language_todo_parsing.md:59`
  - Status: open

- **#87** [doc][P1] Add examples section [#789] [blocked:100]
  - File: `test_todo_sample.spl:9`
  - Status: open
  - Blocked by: 100

### gpu

- **#82** [gpu][P1] Create Vector3 variant [#789] [blocked:100,101]
  - File: `test_todo_sample.rs:9`
  - Status: open
  - Blocked by: 100, 101


## P2 Medium Priority TODOs (6)

### doc

- **#49** [doc][P2] Update outdated API examples
  - File: `doc/design/TODO_CONTRIBUTING_UPDATE.md:96`
  - Status: open

### parser

- **#81** [parser][P2] Handle edge case in expression parsing
  - File: `test_todo_sample.rs:6`
  - Status: open

### runtime

- **#88** [runtime][P2] Pointer kinds (unique, shared, weak, handle) require advanced memory FFI
  - File: `tests/system/simple_basic/samples/60_memory_gc_unique_shared_weak_handle.spl:2`
  - Status: open

- **#89** [runtime][P2] SIMD vector types require FFI implementation
  - File: `tests/system/simple_basic/samples/95_simd_vectors.spl:2`
  - Status: open

### stdlib

- **#59** [stdlib][P2] Parse program path, args, etc.
  - File: `simple/app/dap/server.spl:60`
  - Status: open

### ui

- **#86** [ui][P2] Improve button click handling
  - File: `test_todo_sample.spl:6`
  - Status: open


## P3 Low Priority TODOs (22)

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
