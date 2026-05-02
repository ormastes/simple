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
