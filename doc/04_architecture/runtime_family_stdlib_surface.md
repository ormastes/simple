# Runtime Family Stdlib Surface Audit

> Agent 4 deliverable for GC/no-GC runtime multi-agent completion plan.
> Companion document to `runtime_family_support_matrix.md`.
> Updated 2026-04-04.

## 1. Module Inventory Per Family

### 1.1 `common` (799 files, ~30+ sub-modules)

Pure utility library. No mutation, no async, no FFI.

| Sub-module | Purpose |
|------------|---------|
| `aes/`, `bcrypt/`, `crypto/` | Cryptography |
| `base64/`, `base_encoding/`, `cbor/`, `csv/`, `avro/` | Encoding/serialization |
| `collections/`, `avl_tree/`, `b_tree/`, `bloom_filter/`, `fenwick_tree/` | Data structures |
| `color/`, `complex/`, `fraction/`, `geometry/`, `fft/` | Math/science |
| `date/`, `uuid/` | Date/time, identifiers |
| `json/`, `sdn/` | Data formats |
| `regex/` | Pattern matching |
| `text/`, `encoding/` | Text processing |
| `animation/`, `ascii_art/` | Output formatting |
| `compute/`, `core/`, `engine/` | Compute primitives |
| `diagnostics/`, `diff/`, `doctest/`, `fsm/`, `gpu/` | Developer tools |
| Root `.spl` files | error, format, functional, hash, json, math, option, result, string, table, tap, target, text, traits, types, validation, ... |

### 1.2 `nogc_sync_mut` (835 files, 63 sub-modules)

Largest family. Primary systems-programming library.

| Sub-module | Purpose |
|------------|---------|
| `benchmark/` | Benchmarking framework |
| `buffer/`, `cache/` | Memory management |
| `cli/`, `cli_output/` | Command-line interfaces |
| `compositor/` | UI composition |
| `compress/`, `compression/` | Data compression |
| `cuda/`, `gpu/`, `gpu_driver/`, `gpu_runtime/` | GPU support |
| `daemon_sdk/` | Background service framework |
| `dap/` | Debug Adapter Protocol |
| `database/` | Database access |
| `debug/` | Debugging utilities |
| `dependency_tracker/` | Module dependency tracking |
| `diagram/` | Diagram generation |
| `dns/` | DNS resolution |
| `engine/`, `env/` | Runtime engine, environment |
| `examples/` | Example code |
| `failsafe/` | Error recovery |
| `ffi/` | Foreign function interface |
| `file_system/`, `fs/` | Filesystem operations |
| `hooks/` | Hook system |
| `http/`, `http_client/`, `http_server/` | HTTP protocol |
| `io/` | I/O abstractions |
| `jit/` | JIT compilation support |
| `kafka/`, `mqtt/`, `stomp/` | Message brokers |
| `lsp/` | Language Server Protocol |
| `mcp/`, `mcp_sdk/` | Model Context Protocol |
| `mem_tracker/` | Memory tracking |
| `net/`, `tcp/`, `tls/`, `websocket/` | Networking |
| `oauth/` | Authentication |
| `package/` | Package management |
| `platform/` | Platform abstraction |
| `ptr/` | Pointer utilities |
| `qemu/` | QEMU integration |
| `runtime/` | Runtime support |
| `sanitizer/` | Memory sanitizer |
| `shell/` | Shell integration |
| `smtp/` | Email protocol |
| `spec/` | Test specification framework |
| `src/` | Source utilities |
| `terminal/`, `tmux/` | Terminal handling |
| `test/`, `testing/`, `test_runner/` | Test infrastructure |
| `torch/` | ML framework bindings |
| `tui/` | Text UI framework |
| `ui_test/` | UI testing |
| `unsafe/` | Unsafe operations |
| `web_ui/` | Web UI |
| Root `.spl` files | allocator, array, atomic, binary_io, conf, db_atomic, debug, dig, fs, fuzz, gc, glob, io, io_runtime, lazy_val, log, net, path, perf, platform, process_limits, process_monitor, rc, resource_tracker, runtime_value, runtime_wrappers, simd, spec, spipe, timing |

### 1.3 `nogc_async_mut` (181 files, 13 sub-modules)

Async runtime with actor model and OTP-style supervision.

| Sub-module | Purpose |
|------------|---------|
| `actor/`, `actors/` | Actor model implementation |
| `async/`, `async_host/` | Async runtime (embedded + host) |
| `concurrent/` | Concurrent data structures (MPSC, MPMC, ConcurrentMap) |
| `cuda/`, `gpu/` | GPU async operations |
| `http_server/` | Async HTTP server |
| `io/` | Async I/O |
| `llm/` | LLM integration |
| `mcp/` | Async MCP |
| `ml/`, `torch/` | Machine learning |
| Root `.spl` files | actor_heap, actor_scheduler, async, async_embedded, async_host, async_sffi, async_unified, concurrent, coroutine, effects, gen_event, gen_server, gen_statem, generator, mailbox, mailbox_actor, monitor, supervisor, thread_pool, thread_sffi |

### 1.4 `gc_async_mut` (46 files, 5 sub-modules)

GPU/ML-focused family requiring GC runtime.

| Sub-module | Purpose |
|------------|---------|
| `cuda/` | CUDA kernel management |
| `gpu/` | GPU operations and memory |
| `gpu_runtime/` | GPU runtime support |
| `io/` | GC-managed I/O |
| `torch/` | PyTorch bindings |
| Root `.spl` file | gpu (all GPU operations, BLAS-like ops) |

### 1.5 `nogc_async_immut` (22 files, 11 sub-modules)

Persistent data structures with structural sharing.

| Sub-module | Purpose |
|------------|---------|
| `actor_snapshot/` | Zero-copy actor state snapshots |
| `atom/` | CAS-based mutable references to immutable values |
| `combinators/` | Functional combinators (pmap, pfilter, pfold) |
| `persistent_list/` | Cons list (O(1) prepend) |
| `persistent_map/` | HAMT-based immutable hash map |
| `persistent_set/` | Immutable set |
| `persistent_sorted_map/` | LLRB red-black tree |
| `persistent_trie/` | Prefix tree |
| `persistent_vec/` | RRB-tree backed immutable vector |
| `ref/` | Validated atom with state transition guards |
| `versioned/` | MVCC version-stamped snapshots |

### 1.6 `nogc_async_mut_noalloc` (90 files, 13 sub-modules)

Baremetal runtime. Stack-only, no heap allocation.

| Sub-module | Purpose |
|------------|---------|
| `async/` | Cooperative coroutines (fixed task slots) |
| `baremetal/` | Architecture HAL (arm, arm64, riscv, riscv32, x86, x86_64) |
| `collections/` | Fixed-size arrays, maps, sets, stacks, ring buffers |
| `execution/` | Runtime execution context |
| `hash/` | FNV-1a, CRC32 |
| `io/` | Semihost/UART I/O |
| `log/` | Structured logging |
| `math/` | Integer math |
| `memory/` | Reference-counted binary, shared heap config |
| `path/` | Semihost path handling |
| `qemu/` | QEMU boot test runner |
| `sort/` | In-place sorting, binary search |
| `string/` | Allocation-free string ops |

---

## 2. Cross-Family Module Overlap Analysis

Modules that exist in multiple families, showing intentional specialization:

| Capability | `common` | `nogc_sync_mut` | `nogc_async_mut` | `gc_async_mut` | `nogc_async_mut_noalloc` |
|------------|----------|-----------------|-------------------|----------------|--------------------------|
| **I/O** | -- | `io/`, `io_runtime`, `fs/` | `io/` (async) | `io/` (GC-managed) | `io/` (semihost/UART) |
| **GPU** | `gpu/` (pure types) | `gpu/`, `gpu_driver/`, `gpu_runtime/` | `cuda/`, `gpu/` | `cuda/`, `gpu/`, `gpu_runtime/` | -- |
| **Collections** | `collections/` (pure) | `array`, `rc` | `concurrent` (MPSC/MPMC) | -- | `collections/` (fixed-size) |
| **Math** | `math` (full) | -- | -- | -- | `math/` (integer only) |
| **String/Text** | `text`, `string_core` | `string_core` (re-export) | -- | -- | `string/` (alloc-free) |
| **Hashing** | `hash_utils` | -- | -- | -- | `hash/` (stack-based) |
| **Sorting** | `algorithm_utils` | -- | -- | -- | `sort/` (in-place) |
| **Logging** | -- | `log` | -- | -- | `log/` (bare-metal) |
| **Path** | -- | `path` | -- | -- | `path/` (semihost) |
| **Testing** | -- | `spec/`, `spipe` | -- | -- | -- |
| **Networking** | -- | `net/`, `tcp/`, `tls/`, `http*/`, `websocket/`, `dns/`, `smtp/`, `mqtt/`, `kafka/`, `stomp/` | `http_server/` (async) | -- | -- |
| **ML/Torch** | -- | `torch/` | `ml/`, `torch/`, `llm/` | `torch/` | -- |
| **MCP** | -- | `mcp/`, `mcp_sdk/` | `mcp/` | -- | -- |
| **Actors** | -- | -- | `actor/`, `actors/`, `supervisor`, `gen_server`, `gen_statem`, `gen_event` | -- | -- |
| **Async** | `async_core` (types) | -- | `async/`, `async_host/`, `async_embedded` | -- | `async/` (noalloc) |
| **QEMU** | -- | `qemu/` | -- | -- | `qemu/` |
| **Baremetal** | -- | -- | -- | -- | `baremetal/` (6 arch HALs) |

---

## 3. Intentional Differences

These differences are by design and should NOT be filled:

| Difference | Family | Reason |
|------------|--------|--------|
| No networking | `nogc_async_mut_noalloc` | Baremetal has no TCP/IP stack; uses UART/semihost |
| No testing framework | `nogc_async_mut_noalloc` | Tests run via QEMU boot runner, not `spec` |
| No GPU | `nogc_async_mut_noalloc` | Baremetal targets lack GPU drivers |
| Only GPU/ML modules | `gc_async_mut` | This family exists specifically for GC-managed GPU memory |
| No `me` on data structures | `nogc_async_immut` | Persistent data structures return new versions |
| No general I/O | `gc_async_mut` | GPU I/O is via host-side `nogc_sync_mut` |
| Actors only in `nogc_async_mut` | -- | Actor model requires async + mutable state |
| `common` has no SFFI | -- | Pure functions by design |

---

## 4. Accidental Gaps Found

| Gap | Severity | Fix | Status |
|-----|----------|-----|--------|
| **`nogc_async_mut_noalloc` missing root `__init__.spl`** | High | Created with `@no_gc`, `pub mod` declarations, and re-exports from all 13 sub-modules | **Fixed** (this PR) |
| **`nogc_async_immut.__init__.spl` exports only version fn** | Medium | Should re-export `PersistentMap`, `PersistentVec`, `Atom`, `Ref`, core types from sub-modules | Deferred (Gap 9 in support matrix) |
| **`nogc_async_immut` not in interpreter search path** | Medium | Add to module loader search order after `common` | Deferred (Gap 3 in support matrix, Agent 3) |
| **`gc_sync_mut` tests exist without source** | Low | Relocate tests to `nogc_sync_mut` or create family | Decision pending (Gap 6) |
| **Duplicate GPU modules** | Low | `gpu/` exists in `common`, `nogc_sync_mut`, `nogc_async_mut`, `gc_async_mut` with overlapping but different APIs | Intentional layering (pure types vs sync vs async vs GC) |
| **Duplicate `compress/` and `compression/`** in `nogc_sync_mut` | Low | Likely accidental duplication; should consolidate | Not yet tracked |

---

## 5. Recommendations

### 5.1 Immediate (this PR)
- [x] Create `nogc_async_mut_noalloc/__init__.spl` with full exports
- [x] Document module surface per family

### 5.2 Near-term (subsequent PRs)
- [ ] Enrich `nogc_async_immut/__init__.spl` with core type exports (Agent 4 follow-up)
- [ ] Add `nogc_async_immut` to interpreter module loader search order (Agent 3)
- [ ] Consolidate `compress/` and `compression/` in `nogc_sync_mut`
- [ ] Resolve `gc_sync_mut` orphaned tests (relocate to `nogc_sync_mut`)

### 5.3 Deferred (not needed now)
- Do NOT create `gc_sync_immut`, `gc_sync_mut`, `nogc_sync_immut` directories
- Do NOT add networking to `nogc_async_mut_noalloc`
- Do NOT add testing framework to `nogc_async_mut_noalloc`

---

## 6. Root `__init__.spl` Assessment

The root `src/lib/__init__.spl` does NOT explicitly reference family directories. Family resolution is handled entirely by the interpreter module loader's hardcoded search order in `src/compiler/10.frontend/core/interpreter/module_loader.spl`.

The root init file re-exports from root-level `.spl` files (which live in `nogc_sync_mut` primarily) and declares `pub mod` for shared sub-modules (`report`, `common`, `type`, `sdn`, `mcp`, `src`).

No changes to `src/lib/__init__.spl` are needed for family parity.
