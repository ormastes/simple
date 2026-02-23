# Plan: src/ Directory Refactor — `src/lib/` as the new `std.*` home

**Date:** 2026-02-19
**Status:** Draft

---

## Core Design Decision

**`src/lib/` → renamed to `src/lib/`** — the folder name changes, but the `std.*` import namespace stays.
`src/lib/` becomes the single home for everything that was `std.*` AND `lib.*`.

The build config (`simple.sdn`) maps `std.*` to `src/lib/`, eliminating the `lib.*` namespace entirely.

---

## Target `src/` Structure (after refactor)

```
src/
  app/              # Unchanged — ~600 files, 90+ subdirs
  compiler/         # Unchanged — full compiler backends
  compiler_core/    # Unchanged — bootstrap core
  compiler_seed/    # Unchanged — C++ bootstrap
  compiler_shared/  # Shared infra + interpreter/ (absorbed from shared_compiler/)
  i18n/             # Unchanged
  lib/              # NEW NAME for std — all standard library content
```

**Eliminated from `src/` root:** `std/`, `lib/` (old), `ffi/`, `mcp_lib/`, `baremetal/`,
`blocks/`, `blocks.spl`, `shared_compiler/`, `bin_simple/`, `compiler_core_win/`

---

## Target `src/lib/` Structure

```
src/lib/                            # (was src/lib/ + src/lib/ merged)
  simple.sdn                        # updated project config

  # ── Core language features (all from old std/) ────────────────
  option.spl, result.spl, traits.spl, convert.spl, functions.spl
  array.spl, text.spl, math.spl, log.spl, error.spl, debug.spl
  async.spl, async_core.spl, concurrent.spl, atomic.spl
  spec/, sspec.spl, testing/

  # ── Data Structures (old std/) ───────────────────────────────
  map/, queue/, linked_list/, tree/, avl_tree/, red_black_tree/
  b_tree/, skip_list/, trie/, interval_tree/, segment_tree/
  buffer/, cache/, rope/, lazy/, sorting/, graph/

  # ── Math & Algorithms (old std/) ─────────────────────────────
  complex/, fraction/, linear_algebra/, numerical_methods/
  optimization/, statistics/, fft/, signal_processing/

  # ── Encoding & Serialization (old std/) ──────────────────────
  json/          # merged: old std/json/ (10 files) + old lib/json/ (builder.spl)
  sdn/, yaml/, xml/, csv/, html/, markdown/, cbor/, msgpack/
  protobuf/, avro/, base64/, base_encoding/, compression/, huffman/

  # ── Networking (old std/) ────────────────────────────────────
  net/, http/, http_client/, http_server/, tcp/, dns/, websocket/
  mqtt/, kafka/, smtp/, stomp/, uri/, tls/

  # ── Crypto (old std/) ────────────────────────────────────────
  crypto/, aes/, bcrypt/, scrypt/, rsa/, signature/, jwt/, cert/

  # ── Async & I/O (old std/) ───────────────────────────────────
  async/, async_host/, file_system/, platform/, date/, env/

  # ── CLI & Parsing (merged std/ + lib/) ───────────────────────
  cli/           # merged: old std/cli/ (8 files) + old lib/cli/ (5 files)
  parser/        # merged: old std/parser/ + old lib/parser/ (ast, lexer, parser)

  # ── Report, Template, Format (old std/) ──────────────────────
  report/, template/, format_utils.spl, locale/

  # ── ML / GPU / AI (moved from old lib/) ──────────────────────
  pure/          # ML tensor library (60+ files, from lib/pure/)
  cuda/          # CUDA integration (from lib/cuda/)
  torch/         # PyTorch FFI (from lib/torch/)
  gpu/           # GPU compute (already in std/)
  compute/       # Compute device management (already in std/)

  # ── Data Infrastructure (moved from old lib/) ────────────────
  database/      # BugDB/TestDB/FeatureDB (from lib/database/)
  mcp_sdk/       # MCP SDK (from lib/mcp_sdk/)
  collections/   # Advanced collections (from lib/collections/)
  execution/     # Execution engine (from lib/execution/)
  hooks/         # Event hooks (from lib/hooks/)
  memory/        # Memory mgmt (from lib/memory/)
  diagnostics/   # Diagnostic reporting (from lib/diagnostics/)
  qemu/          # QEMU integration (from lib/qemu/)

  # ── Root lib/ files (from old lib/ root) ─────────────────────
  actor_scheduler.spl, lazy_val.spl, mailbox.spl
  message_transfer.spl, symbol.spl, types.spl, perf.spl

  # ── FFI layer (moved from src/ffi/) ──────────────────────────
  ffi/           # io, system, cli, codegen, debug, runtime, ast, error, package, coverage

  # ── MCP Server library (moved from src/mcp_lib/) ─────────────
  mcp/           # merged with existing std/mcp/dap/
    core.spl, protocol.spl, schema.spl, handler_registry.spl
    helpers.spl, category_loaders_v2.spl, lazy_registry_v2.spl
    mod.spl, mod_runtime.spl
    dap/         # (existing DAP types stay)

  # ── Baremetal (moved from src/baremetal/) ────────────────────
  baremetal/     # merged with existing std/baremetal/ (3 files)
    arm/, arm64/, riscv/, riscv32/, x86/, x86_64/, common/
    allocator.spl, interrupt.spl, syscall.spl  (existing 3 kept)
    mod.spl, qemu_runner.spl, string_intern.spl, system_api.spl
```

---

## Phased Execution

### Phase 0 — Configuration (`simple.sdn`)

Update root `simple.sdn`:
- Remove `src/lib` entry from `projects:`
- Keep `src/lib` but configure it as the `std.*` namespace root
- Update all dependency references: `src/lib` replaces `src/lib` everywhere

```diff
  projects:
-   - path: src/lib
    - path: src/lib      # std.* namespace, was src/lib/
  dependencies:
-   src/compiler: [rust, src/lib]
-   src/lib: [rust, src/lib]
-   src/app: [rust, src/compiler, src/lib, src/lib]
-   test: [rust, src/compiler, src/app, src/lib, src/lib]
+   src/compiler: [rust, src/lib]
+   src/app: [rust, src/compiler, src/lib]
+   test: [rust, src/compiler, src/app, src/lib]
```

Update `src/lib/simple.sdn` (absorbs the std project config):
- Remove dependency on `../std` (self is now std)
- Update project name from `simple-lib` to `simple-std`

---

### Phase 1 — Delete dead directories

- `src/bin_simple/` → delete (dead shell script referencing old `target/debug/simple` path)
- `src/compiler_core_win/` → move Python scripts to `tools/windows/`, delete dir

```bash
mkdir -p tools/windows
mv src/compiler_core_win/*.py tools/windows/
mv src/compiler_core_win/ffi_shim.spl tools/windows/
rm -rf src/compiler_core_win/
rm -rf src/bin_simple/
```

---

### Phase 2 — Merge `shared_compiler/` → `compiler_shared/` (4 import sites)

Move `src/shared_compiler/interpreter/` into `src/compiler_shared/interpreter/`.

Update 4 files (change `use shared_compiler.interpreter.` → `use compiler_shared.interpreter.`):
- `src/compiler/linker/wasm_linker.spl`
- `src/compiler/backend/llvm_backend.spl`
- `src/compiler/backend/wasm_backend.spl`
- `src/app/cli/test_compile_import.spl`

Delete `src/shared_compiler/` after updating imports.

---

### Phase 3 — Move `src/ffi/` → `src/lib/ffi/` (11 import sites)

```bash
mv src/ffi/ src/lib/ffi/
```

Update 11 files (`use ffi.X` → `use std.ffi.X`):
- `src/compiler/build_log.spl`
- `src/compiler/project.spl`
- `src/compiler/codegen.spl`
- `src/lib/async_host/future.spl`
- `src/app/debug/remote/ptrace.spl`
- `src/app/debug/remote/dwarf.spl`
- `src/compiler_shared/backend/native_bridge.spl` (3 lines)
- `src/compiler_shared/ffi.spl` (2 lines)

---

### Phase 4 — Move `src/mcp_lib/` → `src/lib/mcp/` (13 import sites)

```bash
cp src/mcp_lib/*.spl src/lib/mcp/
rm -rf src/mcp_lib/
```

Update 13 files (`use mcp_lib.X` → `use std.mcp.X`):
- `src/app/mcp/diag_read_tools.spl`
- `src/app/mcp/debug_tools.spl`
- `src/app/mcp/diag_vcs_tools.spl`
- `src/app/mcp/diag_edit_tools.spl`
- `src/app/mcp/fileio_main.spl`
- `src/app/mcp/main.spl`
- `src/app/mcp/debug_log_tools.spl`
- `src/app/mcp_jj/main.spl`
- `src/app/llm_caret/json_helpers.spl`
- `src/lib/mcp_sdk/core/json.spl`
- `src/mcp_lib/handler_registry.spl` (self-reference, update before moving)
- `src/mcp_lib/category_loaders_v2.spl` (self-reference, update before moving)

---

### Phase 5 — Merge `src/baremetal/` → `src/lib/baremetal/` (8 internal files)

```bash
cp -r src/baremetal/arm src/baremetal/arm64 src/baremetal/riscv \
      src/baremetal/riscv32 src/baremetal/x86 src/baremetal/x86_64 \
      src/baremetal/common src/lib/baremetal/
cp src/baremetal/mod.spl src/baremetal/qemu_runner.spl \
   src/baremetal/string_intern.spl src/baremetal/system_api.spl \
   src/baremetal/test_integration.spl src/baremetal/test_semihost_output.spl \
   src/baremetal/test_system_api_standalone.spl src/lib/baremetal/
rm -rf src/baremetal/
```

Update 8 files (self-referencing imports: `use baremetal.X` → `use std.baremetal.X`):
- `src/baremetal/x86/serial.spl`
- `src/baremetal/x86/semihost.spl`
- `src/baremetal/x86/idt.spl`
- `src/baremetal/x86/serial_test_kernel.spl`
- `src/baremetal/common/test_harness.spl`
- `src/baremetal/arm/startup.spl`
- `src/baremetal/riscv/startup.spl`

Also check `src/app/verify/baremetal.spl` for external references.

---

### Phase 6 — Merge old `src/lib/` → `src/lib/` then rename `src/lib/` → `src/lib/`

#### 6a. Move non-conflicting lib/ subdirs into src/lib/

```bash
mv src/lib/database    src/lib/database
mv src/lib/mcp_sdk     src/lib/mcp_sdk
mv src/lib/pure        src/lib/pure
mv src/lib/collections src/lib/collections
mv src/lib/cuda        src/lib/cuda
mv src/lib/torch       src/lib/torch
mv src/lib/qemu        src/lib/qemu
mv src/lib/execution   src/lib/execution
mv src/lib/hooks       src/lib/hooks
mv src/lib/memory      src/lib/memory
mv src/lib/diagnostics src/lib/diagnostics
```

#### 6b. Move root lib/ files into src/lib/

```bash
mv src/lib/actor_scheduler.spl  src/lib/
mv src/lib/lazy_val.spl         src/lib/
mv src/lib/mailbox.spl          src/lib/
mv src/lib/message_transfer.spl src/lib/
mv src/lib/symbol.spl           src/lib/
mv src/lib/types.spl            src/lib/
mv src/lib/perf.spl             src/lib/
```

#### 6c. Conflict merges

- `src/lib/json/builder.spl` → copy into `src/lib/json/builder.spl` (new file, no conflict)
- `src/lib/cli/*.spl` → merge into `src/lib/cli/` (check for name conflicts first)
- `src/lib/parser/*.spl` → merge into `src/lib/parser/` (check for name conflicts first)

#### 6d. Rename src/lib/ → src/lib/

```bash
mv src/lib src/lib_new
# delete old empty src/lib/
rm -rf src/lib
mv src/lib_new src/lib
```

#### 6e. Update all 106 `use lib.X` → `use std.X` imports

Pattern replacement across all .spl files:
```
use lib.X  →  use std.X
```

---

### Phase 7 — Remove `blocks/` compat shims (50 files)

Delete `src/blocks/` and `src/blocks.spl`:
```bash
rm -rf src/blocks/
rm src/blocks.spl
```

Update 50 files (`use blocks.X` → `use compiler_shared.blocks.X`):

Affected files include:
- `src/compiler/blocks/` (context, resolver, builtin_blocks_*)
- `src/compiler/hir_lowering/types.spl`
- `src/compiler/mir_data.spl`, `mir_lowering.spl`, `frontend.spl`, `driver_types.spl`
- `src/compiler_shared/blocks/` (all files)
- `src/compiler_shared/parser_factory.spl`
- `src/compiler_shared/treesitter/outline.spl`
- `src/compiler_shared/hir_definitions.spl`
- `src/compiler_shared/treesitter_types.spl`
- `src/compiler_shared/treesitter.spl`

---

## Import Change Summary

| Old import | New import | Files |
|-----------|-----------|-------|
| `use shared_compiler.interpreter.` | `use compiler_shared.interpreter.` | 4 |
| `use ffi.X` | `use std.ffi.X` | 11 |
| `use mcp_lib.X` | `use std.mcp.X` | 13 |
| `use baremetal.X` | `use std.baremetal.X` | ~8 |
| `use lib.X` | `use std.X` | 106 |
| `use blocks.X` | `use compiler_shared.blocks.X` | 50 |

**Total: ~192 files modified, ~10 directories moved/merged, 2 directories deleted**

---

## Open Questions

1. **Phase 6 conflict merges** — for `json/`, `cli/`, `parser/` where both `lib/` and `std/` have files: do `lib/` files take precedence, `std/` files take precedence, or merge both side by side?
2. **`src/lib/simple.sdn`** — should the merged lib's `simple.sdn` keep `simple-std` name or a new name?
3. **`src/diagnostics/__init__.spl`** — already deleted per git status; verify no dangling references.

---

## Verification

After each phase:
```bash
bin/simple build          # Check compilation
bin/simple test           # Run all tests
```
