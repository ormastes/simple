# TODO List

**Generated:** 2026-04-14
**Total:** 17 items | **Open:** 17 | **Blocked:** 1 | **Stale:** 0
**Database:** `doc/todo/todo_db.sdn`

## Statistics

### By Area

| Area | Count | P0 | P1 | P2 | P3 | Blocked |
|------|-------|----|----|----|----|---------|
| doc | 1 | 0 | 0 | 1 | 0 | 0 |
| driver | 6 | 0 | 0 | 6 | 0 | 0 |
| gpu | 2 | 0 | 0 | 0 | 2 | 0 |
| parser | 3 | 0 | 0 | 2 | 1 | 0 |
| runtime | 4 | 0 | 0 | 4 | 0 | 1 |
| test | 1 | 0 | 0 | 1 | 0 | 0 |

### By Priority

| Priority | Count | Open | Blocked | Stale |
|----------|-------|------|---------|-------|
| P0 (critical) | 0 | 0 | 0 | 0 |
| P1 (high) | 0 | 0 | 0 | 0 |
| P2 (medium) | 14 | 14 | 1 | 0 |
| P3 (low) | 3 | 3 | 0 | 0 |

## P2 Medium Priority TODOs (13)

### doc

- **#15** [doc][P2] Full implementation of doctest parsing.
  - File: `./src/lib/common/doctest/parser.spl:4`
  - Status: open

### driver

- **#19** [driver][P2] GPU_ACCEL — detect VirtIO-GPU at boot and set global flag
  - File: `./src/os/drivers/gpu/gpu_accel.spl:74`
  - Status: open

- **#20** [driver][P2] interrupt-driven instead of polling
  - File: `./src/os/drivers/virtio/virtio_blk.spl:169`
  - Status: open

- **#21** [driver][P2] zero-copy with proper buffer management
  - File: `./src/os/drivers/virtio/virtio_blk.spl:190`
  - Status: open

- **#22** [driver][P2] Parse IPC message buffer to extract method ID and arguments.
  - File: `./src/os/drivers/virtio/virtio_net_service.spl:113`
  - Status: open

- **#23** [driver][P2] Parse IPC message buffer to extract method ID and arguments.
  - File: `./src/os/services/device_registry/registry.spl:242`
  - Status: open

- **#24** [driver][P2] Parse IPC message buffer to extract method ID and arguments.
  - File: `./src/os/services/pcimgr/pcimgr.spl:207`
  - Status: open

### parser

- **#12** [parser][P2] Add support for generic type aliases
  - File: `./src/compiler_rust/lib/std/src/core/array_ops.spl:492`
  - Status: open

- **#14** [parser][P2] Add support for export * syntax
  - File: `./src/compiler_rust/lib/std/src/mcp/lsp/__init__.spl:4`
  - Status: open

### runtime

- **#25** [runtime][P2] Finish x86_64 baremetal `SpawnBinary` bridge end-to-end.
  - File: `./examples/simple_os/arch/x86_64/boot/baremetal_stubs.c:3438`
  - Status: blocked
  - Blocker: The installed-runtime syscall bridge is linked, but `x64-desktop-disk` still faults on the live `SpawnBinary` path before launch completes. The remaining issue is the x86 baremetal runtime behavior inside the dedicated spawn bridge, not launcher linkage.

- **#10** [runtime][P2] Use real datetime FFI
  - File: `./src/app/package.registry/trust.spl:389`
  - Status: open

- **#11** [runtime][P2] Use real datetime arithmetic
  - File: `./src/app/package.registry/trust.spl:402`
  - Status: open

- **#9** [runtime][P2] Use real datetime FFI when available
  - File: `./src/app/package.registry/signing.spl:282`
  - Status: open

### test

- **#18** [test][P2] restore SRAM readback verify once stm32h7_read_code() is interpreter-safe.
  - File: `./src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl:372`
  - Status: open


## P3 Low Priority TODOs (3)

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
