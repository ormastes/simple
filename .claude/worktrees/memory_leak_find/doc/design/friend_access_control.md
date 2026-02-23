# Friend Access Control

**Status:** Design
**Last Updated:** 2026-02-20

---

## Overview

Friend access control extends the visibility system beyond the binary Public/Private model. It introduces `Internal` and `Package` visibility levels, along with `friend` declarations that grant cross-package access to internal symbols.

---

## Visibility Levels

```simple
enum Visibility:
    Public       # Visible everywhere
    Internal     # Visible to same package + declared friends
    Package      # Visible to same package only
    Private      # Visible to same file only
```

Ordering: `Public > Internal > Package > Private`

The `visibility_meet` operation returns the more restrictive of two levels.

---

## `friend` Declaration

Declared in `__init__.spl` at the top level of a package directory:

```simple
# src/compiler/20.hir/__init__.spl
mod hir

friend types
friend traits
friend mir

export HirModule, HirExpr, HirStmt
internal_export HirLowering, HirBuilder
```

### Semantics

- **Non-transitive:** If A friends B and B friends C, A does NOT get access to C's internals
- **Unidirectional:** `friend types` in `hir/__init__.spl` means the `types` package can see `hir` internals — not the reverse
- **Non-inherited:** Friend status is not inherited by subpackages
- **Scope:** Friend declarations apply to the declaring package and its immediate submodules

### What Friends Can Access

A friend package can access symbols marked with:
- `pub` (Public) — accessible by everyone
- `internal_export` — accessible by friends only
- `pub(friend)` — accessible by friends only (inline modifier)

A friend package still cannot access:
- `pub(package)` — package-internal only
- Private symbols (no modifier)

---

## Visibility Modifiers

### `pub(friend)`

Makes a symbol visible to the declaring module's friends:

```simple
pub(friend) fn lower_hir_to_mir(module: HirModule) -> MirModule:
    # Only accessible from friend packages (types, traits, mir)
    ...
```

### `pub(package)`

Makes a symbol visible within the same package only:

```simple
pub(package) fn internal_validate(node: HirNode) -> bool:
    # Only accessible within the hir package
    ...
```

### `internal_export`

Listed in `__init__.spl` to declare symbols as friend-visible:

```simple
# In __init__.spl
internal_export HirLowering, HirBuilder

# These symbols from submodules are now visible to friend packages
```

This is equivalent to marking those symbols `pub(friend)` but declared at the package level.

---

## Project-Level Friends

Project-wide friend policies can be declared in `simple.sdn`:

```sdn
access:
  friends:
    hir: [types, mir, traits, frontend]
    mir: [hir, types, mir_opt]
    backend: [mir, mir_opt, types, linker]
    driver: [backend, frontend, hir, mir, types]
```

These project-level declarations supplement (not replace) per-package `friend` declarations in `__init__.spl`.

---

## Layer Enforcement

The numbered layer system (see `layered_compiler_architecture.md`) is enforced independently:

1. **Layer rule:** Layer N can only import layers <= N
2. **Friend rule:** Internal symbols require friend declaration
3. **Both must pass:** An import must satisfy both the layer ordering AND the friend/visibility rules

Example:
```
Layer 50 (mir) importing Internal symbol from layer 20 (hir):
  - Layer check: 50 >= 20 ✓
  - Friend check: hir declares "friend mir" ✓
  - Result: ALLOWED

Layer 10 (frontend) importing Internal symbol from layer 20 (hir):
  - Layer check: 10 < 20 ✗
  - Result: DENIED (layer violation, friend check not reached)
```

---

## DirManifest Extension

The `DirManifest` struct (in `dependency/visibility.spl`) gains:

```simple
struct DirManifest:
    name: text
    children: [ModDecl]
    exports: [SymbolId]
    friends: [text]              # Friend package names
    internal_exports: [SymbolId] # Friend-visible symbols
```

---

## Checker Integration

The `VisibilityChecker` (in `visibility_checker.spl`) is extended to:

1. Look up the caller's package
2. Look up the target symbol's visibility level
3. If `Internal`: check if the caller's package is in the target's friend list
4. If `Package`: check if the caller is in the same package
5. If `Private`: check if the caller is in the same file
6. If `Public`: always allow

---

## See Also

- [Layered Compiler Architecture](layered_compiler_architecture.md) — numbered layer system
- [Syntax Quick Reference](../guide/syntax_quick_reference.md) — language syntax
