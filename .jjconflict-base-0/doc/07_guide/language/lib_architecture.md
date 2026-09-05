# Standard Library Architecture Guide

The Simple standard library lives in `src/lib/` and is organized around a
**5-layer mutability model**. Each layer encodes capability constraints so the
compiler can enforce them statically.

---

## 1. Layer Model

| Layer | Dir | GC | Async | Alloc | What belongs here | Examples |
|---|---|---|---|---|---|---|
| Pure | `common/` | No | No | Yes | Stateless transforms, pure functions | `text`, `math`, `json`, `crypto`, `encoding`, `csv`, `statistics`, `linear_algebra` |
| Sync mutable | `nogc_sync_mut/` | No | No | Yes | I/O, filesystem, network, FFI, testing | `ffi`, `fs`, `net`, `http`, `db`, `mcp`, `spec`, `io` |
| Async mutable | `nogc_async_mut/` | No | Yes | Yes | Concurrency primitives | `actors`, `async`, `threads`, `generators` |
| GC + async | `gc_async_mut/` | Yes | Yes | Yes | ML, GPU, browser, high-level runtimes | `gpu`, `cuda`, `torch`, `browser` |
| Baremetal | `nogc_async_mut_noalloc/` | No | Yes | No | Kernel, bare-metal, QEMU, firmware | `execution`, `memory`, `qemu` |

### Decision Tree

```
Does the module allocate heap memory?
  No  → nogc_async_mut_noalloc/   (baremetal only)
  Yes →
    Does it use async/await?
      No  →
        Is it purely functional (no I/O, no mutation)?
          Yes → common/
          No  → nogc_sync_mut/
      Yes →
        Does it need GC (managed object graph)?
          Yes → gc_async_mut/
          No  → nogc_async_mut/
```

---

## 2. Canonical Module Names

Short names are **canonical**. Long names are legacy aliases kept for backward
compatibility and will be removed in a future release.

| Canonical (short) | Legacy (long) | Layer |
|---|---|---|
| `fs` | `file_system` | `nogc_sync_mut/` |
| `db` | `database` | `nogc_sync_mut/` |
| `compress` | `compression` | `nogc_sync_mut/` |
| `net` | *(none)* | `nogc_sync_mut/` |
| `text` | `string` | `common/` |
| `spec` | *(user-facing test framework)* | `nogc_sync_mut/` |
| `testing` | *(internal helpers/mocks)* | `nogc_sync_mut/` |
| `test` | *(test data/fixtures)* | `nogc_sync_mut/` |

**`text` vs `string`:** `text` is canonical (1308 import uses vs 286 for
`string`). `string` is a deprecated alias; new code must use `text`.

**`spec` / `testing` / `test` distinction:**
- `spec` — user-facing BDD test framework (`describe`, `it`, `expect`).
- `testing` — internal helpers, mocks, fakes used by the compiler itself.
- `test` — static test data and fixtures (read-only assets).

---

## 3. Import Namespace

The standard library exposes a **two-tier namespace**:

```simple
use std.fs          // short alias — preferred for user code
use std.text        // canonical name

use std.nogc_sync_mut.fs   // layer-qualified — for internal/deep paths only
```

**Rule:** Always prefer `use std.<module>` in application and library code.
Use the layer-qualified form only when disambiguating two modules with the same
short name that exist in different layers (rare).

Modules that appear in multiple layers (async variants of sync modules) follow
this resolution order when the short alias is used:

1. `nogc_sync_mut/` (lowest capability — default for sync code)
2. `nogc_async_mut/` (chosen when inside an `async` context)
3. `gc_async_mut/` (chosen when GC is enabled for the compilation unit)

---

## 4. Module Layout

```
src/lib/<layer>/<module>/
  mod.spl          # Public exports (re-exports from sub-files)
  types.spl        # Type definitions, structs, enums
  impl.spl         # Core implementation
  utils.spl        # Internal helpers (not exported)
```

- `mod.spl` (or `__init__.spl` for legacy modules) is the entry point.
- Maximum **800 lines per file**. Split into sub-files when exceeded.
- Exported symbols must appear in `mod.spl`; unexported helpers stay in
  `utils.spl` and must not be re-exported.

---

## 5. Known Issues & Migration Plan

### `src/` Subdirectory Anomaly
Four layers contain a `<layer>/src/collections/`, `<layer>/src/core/` etc.
sub-tree (a Cargo-style artifact that does not belong). These will be
**flattened**: contents move to the layer root and the `src/` directory is
deleted. No action needed from library authors; the migration is automated.

### Paired Directory Names (Complementary, Not Duplicates)

These directory pairs look like naming inconsistencies but serve distinct architectural roles:

| Short name | Long name | Relationship |
|---|---|---|
| `fs/` | `file_system/` | `fs/` = canonical API (NVMe traits, POSIX driver). `file_system/` = legacy mock/compat shim (zero external callers) |
| `db/` | `database/` | `db/` = storage engine (pager, B-tree, WAL). `database/` = application layer (SQL, FTS, migrations) |
| `compress/` | `compression/` | `compress/` = public API facade. `compression/` = codec internals (gzip, brotli, lz4) |

**Rule:** Short name = public API. Long name = implementation or different layer.
Do NOT merge these pairs — they are complementary. Document with cross-reference
comments in each directory's `mod.spl`.

| Legacy import | Action |
|---|---|
| `use std.string` | Replace with `use std.text` |

Use `bin/simple fix --dry-run` to preview renames before applying.

### Duplication Across Layers
80+ modules appear in more than one layer (e.g., `fs` in both
`nogc_sync_mut/` and `nogc_async_mut/`). This is **by design**: the async
variant wraps the sync API in a non-blocking executor. Do not de-duplicate;
instead ensure both variants expose the same public interface so callers can
switch layers transparently.
