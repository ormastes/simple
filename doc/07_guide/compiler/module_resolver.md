# Module Resolver — Import Resolution Guide

## How Imports Resolve

The module resolver maps `use X.Y.Z` to filesystem paths using these strategies **in order**:

| Priority | Strategy | Example | Resolves to |
|----------|----------|---------|-------------|
| 1 | **Relative** from importing file's parent dir | `use sibling.foo` from `src/app/cli/main.spl` | `src/app/cli/sibling/foo.spl` |
| 2 | **Absolute** via `crate.*` prefix | `use crate.app.cli.main` | `{source_root}/app/cli/main.spl` |
| 3 | **Stdlib** for `std.*` / `lib.*` prefix | `use std.io` | `src/lib/*/io.spl` (searches subdirs) |
| 4 | **Compiler** for `compiler.*` prefix | `use compiler.mir.mir_data` | `src/compiler/50.mir/mir_data.spl` |
| 5 | **Numbered dir** at source_root | `use tools.ffi_gen` | `src/NN.tools/ffi_gen.spl` |
| 6 | **Source root fallback** | `use app.ffi_gen.parser` | `src/app/ffi_gen/parser.spl` |

### Source Root Fallback (Strategy 6)

When all other strategies fail, the resolver checks if `segments[0]` matches a **directory** under `source_root` (`src/`). If it does, resolution continues from there.

This means **any directory under `src/` is a valid top-level import namespace**:

```simple
use app.ffi_gen.parser       # → src/app/ffi_gen/parser.spl
use os.kernel.boot.cpu       # → src/os/kernel/boot/cpu.spl
use compiler.tools.stats     # → src/compiler/90.tools/stats.spl (via numbered dir)
```

### Numbered Directory Prefix Stripping

Directories matching `NN.name` (1-3 digit prefix + dot) are found by their `name` part:

```
src/compiler/00.common/   → use compiler.common.*
src/compiler/10.frontend/ → use compiler.frontend.*
src/compiler/90.tools/    → use compiler.tools.*
```

## Stdlib Resolution (Strategy 3) — Two Independent Axes

`std.*` and `lib.*` imports do **not** name a memory-model tree directly. Resolution
walks two orthogonal axes:

### Axis 1 — Memory-model tree (capability family), by fallback order

The leading `std` / `std_lib` segment is stripped, then the remaining path is searched
under each family directory **in this fixed order** (`module_loader.rs`, `resolve_from_stdlib_root`):

```
nogc_async_mut → nogc_sync_mut → nogc_async_immut → common → gc_async_mut → nogc_async_mut_noalloc
```

First match wins. The **host default family is `async_nogc_mut`** (async + no-GC + mutable).
So `use std.io.tcp` finds `nogc_async_mut/io/tcp.spl` if present, otherwise falls through
to `nogc_sync_mut/io/tcp.spl`, and so on. The tree is therefore **selected by availability
+ fallback order, not by a per-import or per-build config knob today.** (A true config-driven
family selector does not exist yet — treat requests for one as a feature, not a bug.)

Implication, and the rule that prevents this whole class of breakage:

- **Tree-neutral abstractions** (e.g. the I/O traits `Read`/`Write`/`Seek`/`Close` and types
  `IoError`/`SeekFrom`, JSON helpers, bcrypt) live once in **`common/`** and are imported as
  `std.io.traits` / `lib.common.io.traits` — both resolve to `src/lib/common/io/traits.spl`
  via the fallback. They must NOT be duplicated per family.
- **Tree-specific implementations** (`io/file.spl`, `io/tcp.spl`, event loops) live in the
  family dir that owns their capability.
- A module that exists in only one family but is imported by another is **import debt**, not a
  resolver feature. Fix it by adding a facade module or rewriting the import — do **not** widen
  the cross-family fallback. (See `doc/03_plan/import_warning_debt_2026-05-13.md`, Next Actions 1–2.)

#### `std.io` single-segment shim

As a special case, the bare single-segment import `use std.io` (no third segment) is shimmed
directly to `nogc_sync_mut/io/__init__.spl`. Multi-segment forms like `std.io.traits` do **not**
hit the shim — they go through the Axis-1 fallback above.

### Axis 2 — SIMD hardware tier (orthogonal to the family)

Independently, `stdlib_variant.rs` prepends hardware-specific roots `variants/<tier>/`
(`x86_64_avx512`, `x86_64_avx2`, `x86_64_sse2`, …) ahead of the base root, chosen from the
active SIMD tier (`SIMPLE_SIMD_TIER`, host CPU detection). This selects an optimized copy of a
module when one exists; it does **not** change which capability family is used. Scalar hosts use
the base tree directly.

> History: commit `2cca0bc59c` (2026-05-13) restructured `src/lib` (+1983/−1387 files) and left a
> batch of `common/{io,json,bcrypt}` modules deleted while surviving importers still referenced the
> retired `std.common.io.*` paths. Recovery = recreate those modules under `common/` and rewrite
> importers to `std.io.*` / `lib.common.*`, per the facade-not-fallback rule above.

## Rules

### NEVER use source symlinks for imports

Symlinks create maintenance burden and break when paths change. The resolver handles all cross-module imports natively:

```
# WRONG: creating symlinks
src/app/ffi_gen/parser.spl → ../../compiler/90.tools/ffi_gen/parser.spl

# RIGHT: the resolver resolves directly
# From src/compiler/90.tools/ffi_gen/main.spl:
use app.ffi_gen.parser    # → resolved via source root fallback to src/app/ffi_gen/parser.spl
```

If `use X.Y.Z` doesn't resolve, the fix is to ensure the directory exists under `src/` — not to create symlinks.

### Package data during native-project compilation

Native-project compilation must seed HIR with the types of data declarations
selected by the module's explicit imports and package visibility before strict
MIR lowering. Current-package and ancestor-package exports are visible; an
unqualified name must not bind merely because a declaration with that name is
globally unique in another package. Package-private data is visible to direct
siblings, and underscore-prefixed split directories are transparent to that
package boundary; an ordinary child directory is a distinct package. Untyped
mutable data is `Any`, constants use the same constant-evaluation typing as
normal HIR lowering, and ambiguous named-type owners safely degrade to `Any`.

Keep a negative regression for unrelated package data whenever this selection
logic changes. Undefined names should remain compile errors rather than being
silently satisfied by a global index.

### When `__init__.spl` is needed

`__init__.spl` is only required for:
- **Wildcard re-exports**: `use some.module.*` (the resolver needs `__init__.spl` to know what to export)
- **Directory-level attributes**: `#[no_gc]`, capability restrictions
- **Common uses**: prelude imports shared by all files in the directory

For **fully-qualified imports** like `use os.kernel.boot.cpu.{port_inb}`, no `__init__.spl` is needed — the resolver walks the path directly to the `.spl` file.

### Cross-project imports

Projects declared in `simple.sdn` are directories under `src/`:

```sdn
projects:
  - path: src/compiler
  - path: src/app
  - path: src/lib
```

Cross-project imports work via Strategy 6 (source root fallback). No additional config needed.

## Implementation

Both resolvers implement the same algorithm:

| Resolver | File | Used by |
|----------|------|---------|
| Rust seed | `src/compiler_rust/compiler/src/module_resolver/resolution.rs` | Bootstrap compilation |
| Simple self-hosted | `src/compiler/99.loader/module_resolver/resolution.spl` | Self-hosted compilation |

Changes to one **must** be mirrored in the other.
