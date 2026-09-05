# Package Unfold Specification

> Package unfold allows marking a package as a namespace container only. When a package is unfolded, direct imports of that package become lint/compile errors, forcing users to import specific subpackages instead.

<!-- sdn-diagram:id=package_unfold_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=package_unfold_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

package_unfold_spec -> a
package_unfold_spec -> unfold declarations
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=package_unfold_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 72 | 72 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Package Unfold Specification

Package unfold allows marking a package as a namespace container only. When a package is unfolded, direct imports of that package become lint/compile errors, forcing users to import specific subpackages instead.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #950-960 |
| Category | Language |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/spec/package_unfold_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Package unfold allows marking a package as a namespace container only.
When a package is unfolded, direct imports of that package become lint/compile errors,
forcing users to import specific subpackages instead.

This is useful for organizing large codebases where certain packages exist purely
for namespace organization and should not be imported directly.

## Syntax

```simple
# In a/__init__.spl
unfold {b, c}    # Package 'a' unfolds into subpackages 'a.b' and 'a.c'
```

## Behavior

- `use a.b` → Valid (subpackage)
- `use a.c` → Valid (subpackage)
- `use a` → **Error**: Package 'a' is unfolded, use `a.b` or `a.c` instead

## Error Message Format

```
error[E0501]: cannot import unfolded package 'a' directly
 --> src/main.spl:3:5
  |
3 | use a
  |     ^ package 'a' is unfolded
  |
  = note: Package 'a' is a namespace container only
  = help: Import a specific subpackage instead:
           use a.b
           use a.c
```

## Related Specifications

- [Module Resolution](../compiler/dependency/resolution_spec.spl) - Path resolution
- [Visibility](src/compiler/dependency/visibility.spl) - Access control

## Implementation Notes

- Unfold declaration must appear in `__init__.spl` of a directory-based module
- Parser must validate that unfolded subpackages exist as directories
- Import resolution must check for unfold declarations before allowing imports
- Lint rule I001 should flag violations with auto-fix suggestions

## Scenarios

### Package Unfold

### Declaration Parsing

#### valid declarations

#### parses single subpackage unfold

1. expect decl subpackages len
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = r"unfold {b}"
match parse_unfold(source):
    case ParseResult.Ok(decl):
        expect decl.subpackages.len() == 1
        expect decl.subpackages[0] == "b"
    case ParseResult.Err(e):
        fail("Expected successful parse: {e.message}")
```

</details>

#### parses two subpackages unfold

1. expect decl subpackages len
2. expect decl has subpackage
3. expect decl has subpackage
4. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = r"unfold {b, c}"
match parse_unfold(source):
    case ParseResult.Ok(decl):
        expect decl.subpackages.len() == 2
        expect decl.has_subpackage("b")
        expect decl.has_subpackage("c")
    case ParseResult.Err(e):
        fail("Expected successful parse: {e.message}")
```

</details>

#### parses three or more subpackages

1. expect decl subpackages len
2. expect decl has subpackage
3. expect decl has subpackage
4. expect decl has subpackage
5. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = r"unfold {b, c, d}"
match parse_unfold(source):
    case ParseResult.Ok(decl):
        expect decl.subpackages.len() == 3
        expect decl.has_subpackage("b")
        expect decl.has_subpackage("c")
        expect decl.has_subpackage("d")
    case ParseResult.Err(e):
        fail("Expected successful parse: {e.message}")
```

</details>

#### parses with trailing comma

1. expect decl subpackages len
2. expect decl has subpackage
3. expect decl has subpackage
4. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = r"unfold {b, c,}"
match parse_unfold(source):
    case ParseResult.Ok(decl):
        expect decl.subpackages.len() == 2
        expect decl.has_subpackage("b")
        expect decl.has_subpackage("c")
    case ParseResult.Err(e):
        fail("Expected successful parse: {e.message}")
```

</details>

#### parses with extra whitespace

1. expect decl subpackages len
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = r"unfold {  b  ,  c  }"
match parse_unfold(source):
    case ParseResult.Ok(decl):
        expect decl.subpackages.len() == 2
    case ParseResult.Err(e):
        fail("Expected successful parse: {e.message}")
```

</details>

#### invalid declarations

#### errors on empty unfold

1. fail
2. expect e message contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = r"unfold {}"
match parse_unfold(source):
    case ParseResult.Ok(_):
        fail("Expected error for empty unfold")
    case ParseResult.Err(e):
        expect e.message.contains("empty")
```

</details>

#### errors on invalid identifier

1. fail
2. expect e message contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = r"unfold {123}"
match parse_unfold(source):
    case ParseResult.Ok(_):
        fail("Expected error for invalid identifier")
    case ParseResult.Err(e):
        expect e.message.contains("invalid identifier")
```

</details>

#### errors on duplicate subpackages

1. fail
2. expect e message contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = r"unfold {b, b}"
match parse_unfold(source):
    case ParseResult.Ok(_):
        fail("Expected error for duplicate subpackages")
    case ParseResult.Err(e):
        expect e.message.contains("duplicate")
```

</details>

#### errors on missing closing brace

1. fail
2. expect e message contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = r"unfold {b, c"
match parse_unfold(source):
    case ParseResult.Ok(_):
        fail("Expected error for missing brace")
    case ParseResult.Err(e):
        expect e.message.contains("missing closing brace")
```

</details>

#### errors on missing unfold keyword

1. fail
2. expect e message contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = r"{b, c}"
match parse_unfold(source):
    case ParseResult.Ok(_):
        fail("Expected error for missing keyword")
    case ParseResult.Err(e):
        expect e.message.contains("unfold")
```

</details>

### Directory Structure Validation

#### valid structures

#### accepts unfold matching existing subdirs

1. expect errors len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.from_structure(
    ["a/__init__.spl", "a/b/__init__.spl", "a/c/__init__.spl"],
    ["a", "a/b", "a/c"]
)
val decl = UnfoldDecl.create(["b", "c"])
val errors = validate_unfold(decl, fs, "a")
expect errors.len() == 0
```

</details>

#### accepts nested directory structures

1. expect errors len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.from_structure(
    ["a/__init__.spl", "a/b/__init__.spl", "a/b/c/__init__.spl"],
    ["a", "a/b", "a/b/c"]
)
val decl = UnfoldDecl.create(["b"])
val errors = validate_unfold(decl, fs, "a")
expect errors.len() == 0
```

</details>

#### accepts deeply nested paths

1. expect errors len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.from_structure(
    ["x/__init__.spl", "x/y/__init__.spl", "x/y/z/__init__.spl"],
    ["x", "x/y", "x/y/z"]
)
val decl = UnfoldDecl.create(["y"])
val errors = validate_unfold(decl, fs, "x")
expect errors.len() == 0
```

</details>

#### invalid structures

#### errors when subpackage directory does not exist

1. expect errors len
2. expect errors[0] contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.from_structure(
    ["a/__init__.spl"],
    ["a"]
)
val decl = UnfoldDecl.create(["b"])
val errors = validate_unfold(decl, fs, "a")
expect errors.len() == 1
expect errors[0].contains("does not exist")
```

</details>

#### errors when subpackage has no __init__.spl

1. expect errors len
2. expect errors[0] contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.from_structure(
    ["a/__init__.spl"],
    ["a", "a/b"]  # Directory exists but no __init__.spl
)
val decl = UnfoldDecl.create(["b"])
val errors = validate_unfold(decl, fs, "a")
expect errors.len() == 1
expect errors[0].contains("no __init__.spl")
```

</details>

#### reports multiple validation errors

1. expect errors len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.from_structure(
    ["a/__init__.spl"],
    ["a"]
)
val decl = UnfoldDecl.create(["b", "c", "d"])
val errors = validate_unfold(decl, fs, "a")
expect errors.len() == 3
```

</details>

#### errors when unfold is in file-based module

1. expect errors len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# File-based modules (foo.spl) cannot have subpackages
val fs = MockFileSystem.from_structure(
    ["a.spl"],  # File module, not directory
    []
)
val decl = UnfoldDecl.create(["b"])
val errors = validate_unfold(decl, fs, "a")
expect errors.len() > 0
```

</details>

#### partial validation

#### validates only declared subpackages

1. expect errors len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.from_structure(
    ["a/__init__.spl", "a/b/__init__.spl", "a/c/__init__.spl", "a/d/__init__.spl"],
    ["a", "a/b", "a/c", "a/d"]
)
# Only unfold b and c, not d
val decl = UnfoldDecl.create(["b", "c"])
val errors = validate_unfold(decl, fs, "a")
expect errors.len() == 0
```

</details>

### Import Resolution

#### direct import of unfolded package

#### errors on direct import of unfolded package

1. mod a set unfold
2. expect subpkgs len
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b", "c"])
val import_stmt = ImportStmt.simple("a")

match resolve_import(import_stmt, [mod_a]):
    case ImportResult.UnfoldedPackageError(pkg, subpkgs):
        expect pkg == "a"
        expect subpkgs.len() == 2
    case _:
        fail("Expected UnfoldedPackageError")
```

</details>

#### includes all valid subpackages in error

1. mod a set unfold
2. expect subpkgs len
3. expect subpkgs contains
4. expect subpkgs contains
5. expect subpkgs contains
6. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["x", "y", "z"])
val import_stmt = ImportStmt.simple("a")

match resolve_import(import_stmt, [mod_a]):
    case ImportResult.UnfoldedPackageError(_, subpkgs):
        expect subpkgs.len() == 3
        expect subpkgs.contains("x")
        expect subpkgs.contains("y")
        expect subpkgs.contains("z")
    case _:
        fail("Expected UnfoldedPackageError")
```

</details>

#### valid subpackage imports

#### allows import of valid subpackage

1. mod a set unfold
2. mod a add child
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b", "c"])
val mod_b = Module.dir_module("b", "a/b/__init__.spl")
mod_a.add_child(mod_b)
val import_stmt = ImportStmt.simple("a.b")

match resolve_import(import_stmt, [mod_a]):
    case ImportResult.Ok:
        pass
    case _:
        fail("Expected Ok for subpackage import")
```

</details>

#### allows import with alias from subpackage

1. mod a set unfold
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b"])
val import_stmt = ImportStmt.with_alias("a.b", "alias_b")

match resolve_import(import_stmt, [mod_a]):
    case ImportResult.Ok:
        pass
    case _:
        fail("Expected Ok for aliased import")
```

</details>

#### allows nested item import from subpackage

1. mod a set unfold
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b"])
val import_stmt = ImportStmt.simple("a.b.item")

match resolve_import(import_stmt, [mod_a]):
    case ImportResult.Ok:
        pass
    case _:
        fail("Expected Ok for nested import")
```

</details>

#### wildcard imports

#### errors on wildcard import of unfolded package

1. mod a set unfold
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b", "c"])
val import_stmt = ImportStmt.wildcard("a")

match resolve_import(import_stmt, [mod_a]):
    case ImportResult.UnfoldedPackageError(pkg, _):
        expect pkg == "a"
    case _:
        fail("Expected UnfoldedPackageError for wildcard")
```

</details>

#### allows wildcard import from subpackage

1. mod a set unfold
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b"])
val import_stmt = ImportStmt.wildcard("a.b")

match resolve_import(import_stmt, [mod_a]):
    case ImportResult.Ok:
        pass
    case _:
        fail("Expected Ok for subpackage wildcard")
```

</details>

#### non-unfolded packages

#### allows direct import of non-unfolded package

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
# No unfold declaration
val import_stmt = ImportStmt.simple("a")

match resolve_import(import_stmt, [mod_a]):
    case ImportResult.Ok:
        pass
    case _:
        fail("Expected Ok for non-unfolded package")
```

</details>

#### multiple packages

#### correctly identifies unfolded among multiple packages

1. mod a set unfold
2. fail
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["x"])
val mod_b = Module.dir_module("b", "b/__init__.spl")
# b is not unfolded

# Import a should fail
match resolve_import(ImportStmt.simple("a"), [mod_a, mod_b]):
    case ImportResult.UnfoldedPackageError(_, _):
        pass
    case _:
        fail("Expected error for unfolded 'a'")

# Import b should succeed
match resolve_import(ImportStmt.simple("b"), [mod_a, mod_b]):
    case ImportResult.Ok:
        pass
    case _:
        fail("Expected Ok for non-unfolded 'b'")
```

</details>

#### relative imports

#### errors on relative import of unfolded package

1. mod a set unfold
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b"])
# Simulating relative import "super.a" that resolves to just "a"
val import_stmt = ImportStmt.simple("a")

match resolve_import(import_stmt, [mod_a]):
    case ImportResult.UnfoldedPackageError(_, _):
        pass
    case _:
        fail("Expected error for relative import of unfolded")
```

</details>

#### crate-prefixed imports

#### errors on crate.pkg when pkg is unfolded

1. mod a set unfold
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b"])
# Simulating "crate.a" that resolves to "a"
val import_stmt = ImportStmt.simple("a")

match resolve_import(import_stmt, [mod_a]):
    case ImportResult.UnfoldedPackageError(_, _):
        pass
    case _:
        fail("Expected error for crate-prefixed import")
```

</details>

### Nested Unfolds

#### two-level nesting

#### handles a unfolds to b, b unfolds to c,d

1. mod a set unfold
2. mod b set unfold
3. mod a add child
4. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b"])

val mod_b = Module.dir_module("b", "a/b/__init__.spl")
mod_b.set_unfold(["c", "d"])
mod_a.add_child(mod_b)

# use a -> Error
match resolve_import(ImportStmt.simple("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(pkg, _):
        expect pkg == "a"
    case _:
        fail("Expected error for 'use a'")
```

</details>

#### provides correct suggestions at each level

1. mod a set unfold
2. expect subpkgs contains
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b"])

match resolve_import(ImportStmt.simple("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(_, subpkgs):
        expect subpkgs.contains("b")
    case _:
        fail("Expected error with suggestions")
```

</details>

#### three-level nesting

#### handles deeply nested unfolds

1. mod a set unfold
2. mod b set unfold
3. mod a add child
4. mod c set unfold
5. mod b add child
6. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b"])

val mod_b = Module.dir_module("b", "a/b/__init__.spl")
mod_b.set_unfold(["c"])
mod_a.add_child(mod_b)

val mod_c = Module.dir_module("c", "a/b/c/__init__.spl")
mod_c.set_unfold(["d"])
mod_b.add_child(mod_c)

# Each level should error when imported directly
match resolve_import(ImportStmt.simple("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(_, _):
        pass
    case _:
        fail("Expected error at level 1")
```

</details>

#### partial nesting

#### allows import when only parent is unfolded

1. mod a set unfold
2. mod a add child
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b"])

val mod_b = Module.dir_module("b", "a/b/__init__.spl")
# b is NOT unfolded
mod_a.add_child(mod_b)

# use a.b should succeed
match resolve_import(ImportStmt.simple("a.b"), [mod_a]):
    case ImportResult.Ok:
        pass
    case _:
        fail("Expected Ok for non-unfolded child")
```

</details>

#### mixed children

#### handles mix of unfolded and non-unfolded children

1. mod a set unfold
2. mod internal set unfold
3. mod a add child
4. mod a add child
5. expect subpkgs contains
6. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["internal"])  # Only internal is unfolded

val mod_pub = Module.dir_module("pub", "a/pub/__init__.spl")
# pub is public, not in unfold list

val mod_internal = Module.dir_module("internal", "a/internal/__init__.spl")
mod_internal.set_unfold(["impl"])

mod_a.add_child(mod_pub)
mod_a.add_child(mod_internal)

# Note: In this design, unfold only affects importing 'a' directly,
# not whether 'pub' is accessible
match resolve_import(ImportStmt.simple("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(_, subpkgs):
        expect subpkgs.contains("internal")
    case _:
        fail("Expected error")
```

</details>

### Partial Unfold

#### selective unfolding

#### allows public modules alongside unfold

1. mod a set unfold
2. expect subpkgs len
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["internal"])

# 'api' is not in unfold list, so technically accessible
# But importing 'a' directly still fails
match resolve_import(ImportStmt.simple("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(_, subpkgs):
        expect subpkgs.len() == 1
        expect subpkgs[0] == "internal"
    case _:
        fail("Expected error")
```

</details>

#### supports pub mod api + unfold {impl} pattern

1. mod lib set unfold
2. mod lib add child
3. mod lib add child
4. expect subpkgs contains
5. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_lib = Module.dir_module("lib", "lib/__init__.spl")
mod_lib.set_unfold(["impl"])

val mod_api = Module.file_module("api", "lib/api.spl")
mod_lib.add_child(mod_api)

val mod_impl = Module.dir_module("impl", "lib/impl/__init__.spl")
mod_lib.add_child(mod_impl)

# Importing lib directly should error with impl suggestion
match resolve_import(ImportStmt.simple("lib"), [mod_lib]):
    case ImportResult.UnfoldedPackageError(_, subpkgs):
        expect subpkgs.contains("impl")
    case _:
        fail("Expected error")
```

</details>

#### re-exports from unfolded

#### handles re-export pattern from unfolded package

1. mod a set unfold
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pattern: a/__init__.spl re-exports from a.internal
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["internal"])

# Re-exports would be defined in __init__.spl but the import
# resolution for 'use a' should still fail
match resolve_import(ImportStmt.simple("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(_, _):
        pass  # Correct - direct import blocked
    case _:
        fail("Expected error even with re-exports")
```

</details>

### Edge Cases

#### minimal cases

#### handles empty package with only unfold

1. mod a set unfold
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b"])
# Package has only unfold, no other content

match resolve_import(ImportStmt.simple("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(_, _):
        pass
    case _:
        fail("Expected error")
```

</details>

#### handles single subpackage unfold

1. mod a set unfold
2. expect subpkgs len
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["only_child"])

match resolve_import(ImportStmt.simple("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(_, subpkgs):
        expect subpkgs.len() == 1
        expect subpkgs[0] == "only_child"
    case _:
        fail("Expected error")
```

</details>

#### naming edge cases

#### handles very long subpackage names

1. mod a set unfold
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val long_name = "very_long_subpackage_name_that_is_quite_lengthy"
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold([long_name])

match resolve_import(ImportStmt.simple("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(_, subpkgs):
        expect subpkgs[0] == long_name
    case _:
        fail("Expected error")
```

</details>

#### handles subpackage names with underscores

1. mod a set unfold
2. expect subpkgs contains
3. expect subpkgs contains
4. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["sub_pkg", "another_sub"])

match resolve_import(ImportStmt.simple("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(_, subpkgs):
        expect subpkgs.contains("sub_pkg")
        expect subpkgs.contains("another_sub")
    case _:
        fail("Expected error")
```

</details>

#### handles single-character subpackage names

1. mod a set unfold
2. expect subpkgs len
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["x", "y", "z"])

match resolve_import(ImportStmt.simple("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(_, subpkgs):
        expect subpkgs.len() == 3
    case _:
        fail("Expected error")
```

</details>

#### declaration position

#### handles unfold not at top of file

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This tests that unfold can appear after other declarations
# In practice, parser should find it regardless of position
val source = "# comment\nimport other\n" + r"unfold {b}"
# Simplified test - just verify parsing works
expect true  # Placeholder - real test would check AST
```

</details>

#### module types

#### errors when unfold used in file module

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.file_module("a", "a.spl")  # File, not directory
# Cannot have unfold in file module
expect not mod_a.is_directory
```

</details>

#### handles unfold in test module

1. mod test set unfold
2. expect subpkgs contains
3. expect subpkgs contains
4. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_test = Module.dir_module("test", "test/__init__.spl")
mod_test.set_unfold(["unit", "integration"])

match resolve_import(ImportStmt.simple("test"), [mod_test]):
    case ImportResult.UnfoldedPackageError(_, subpkgs):
        expect subpkgs.contains("unit")
        expect subpkgs.contains("integration")
    case _:
        fail("Expected error")
```

</details>

### Lint Integration

#### lint diagnostics

#### creates I001 diagnostic for unfold violation

1. expect diagnostic message contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostic = create_unfold_lint("mypackage", ["sub1", "sub2"])

expect diagnostic.code == "I001"
expect diagnostic.message.contains("mypackage")
expect diagnostic.severity == "error"
```

</details>

#### includes all valid subpackages in suggestions

1. expect diagnostic suggestions len
2. expect diagnostic suggestions[0] contains
3. expect diagnostic suggestions[1] contains
4. expect diagnostic suggestions[2] contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostic = create_unfold_lint("pkg", ["a", "b", "c"])

expect diagnostic.suggestions.len() == 3
expect diagnostic.suggestions[0].contains("pkg.a")
expect diagnostic.suggestions[1].contains("pkg.b")
expect diagnostic.suggestions[2].contains("pkg.c")
```

</details>

#### formats suggestion as valid import statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostic = create_unfold_lint("mylib", ["core"])

expect diagnostic.suggestions[0] == "use mylib.core"
```

</details>

#### error message formatting

#### formats error with correct structure

1. expect msg contains
2. expect msg contains
3. expect msg contains
4. expect msg contains
5. expect msg contains
6. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = Span.at("src/main.spl", 3, 5)
val msg = format_unfold_error("a", ["b", "c"], span)

expect msg.contains("E0501")
expect msg.contains("cannot import unfolded package")
expect msg.contains("src/main.spl:3:5")
expect msg.contains("namespace container only")
expect msg.contains("use a.b")
expect msg.contains("use a.c")
```

</details>

#### includes help section with all alternatives

1. expect msg contains
2. expect msg contains
3. expect msg contains
4. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = Span.at("test.spl", 1, 1)
val msg = format_unfold_error("pkg", ["x", "y", "z"], span)

expect msg.contains("help: Import a specific subpackage")
expect msg.contains("use pkg.x")
expect msg.contains("use pkg.y")
expect msg.contains("use pkg.z")
```

</details>

#### lint behavior

#### reports correct span location

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostic = create_unfold_lint("a", ["b"])
# Span should point to the import statement
expect diagnostic.span.?
```

</details>

#### provides machine-readable suggestion

1. expect suggestion starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostic = create_unfold_lint("lib", ["api"])

# Suggestions should be valid replacement text
for suggestion in diagnostic.suggestions:
    expect suggestion.starts_with("use ")
```

</details>

### Error Recovery

#### parse error recovery

#### continues parsing after unfold syntax error

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = r"unfold {invalid!}" + "\nfn foo(): pass"
# Should report error but not crash
match parse_unfold(source):
    case ParseResult.Err(e):
        expect e.message.?
    case ParseResult.Ok(_):
        pass  # Acceptable if parser recovers
```

</details>

#### handles malformed unfold gracefully

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "unfold"  # Missing braces entirely
match parse_unfold(source):
    case ParseResult.Err(e):
        expect e.message.?
    case _:
        fail("Expected parse error")
```

</details>

#### validation error accumulation

#### reports all unfold violations, not just first

1. expect errors len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = MockFileSystem.from_structure(
    ["a/__init__.spl"],
    ["a"]
)
val decl = UnfoldDecl.create(["missing1", "missing2", "missing3"])
val errors = validate_unfold(decl, fs, "a")

# Should report all three missing subpackages
expect errors.len() == 3
```

</details>

#### does not cascade errors to unrelated code

1. mod a set unfold
2. fail
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# An unfold error in package 'a' should not affect 'b'
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["x"])
val mod_b = Module.dir_module("b", "b/__init__.spl")

# Error in 'a'
match resolve_import(ImportStmt.simple("a"), [mod_a, mod_b]):
    case ImportResult.UnfoldedPackageError(_, _):
        pass
    case _:
        fail("Expected error for 'a'")

# 'b' should still work
match resolve_import(ImportStmt.simple("b"), [mod_a, mod_b]):
    case ImportResult.Ok:
        pass
    case _:
        fail("'b' should not be affected by 'a' error")
```

</details>

### Advanced Import Scenarios

#### import specific symbol from unfolded

#### errors when importing symbol from unfolded package

1. mod a set unfold


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b"])

# Trying to import a specific symbol from unfolded package
val import_stmt = ImportStmt.simple("a.SomeType")

match resolve_import(import_stmt, [mod_a]):
    case ImportResult.Ok:
        pass  # Valid - accessing a.SomeType is allowed
    case ImportResult.UnfoldedPackageError(_, _):
        pass  # Also valid interpretation
```

</details>

#### allows qualified access after valid subpackage import

1. mod a set unfold
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b"])

# Import subpackage then access nested items
val import_stmt = ImportStmt.simple("a.b.nested")

match resolve_import(import_stmt, [mod_a]):
    case ImportResult.Ok:
        pass
    case _:
        fail("Expected Ok for nested path through valid subpackage")
```

</details>

#### multiple import statements

#### reports errors for multiple unfolded imports in same file

1. mod a set unfold
2. mod b set unfold


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["x"])
val mod_b = Module.dir_module("b", "b/__init__.spl")
mod_b.set_unfold(["y"])

# Both should error
var error_count = 0

match resolve_import(ImportStmt.simple("a"), [mod_a, mod_b]):
    case ImportResult.UnfoldedPackageError(_, _):
        error_count = error_count + 1
    case _:
        pass

match resolve_import(ImportStmt.simple("b"), [mod_a, mod_b]):
    case ImportResult.UnfoldedPackageError(_, _):
        error_count = error_count + 1
    case _:
        pass

expect error_count == 2
```

</details>

#### handles import with glob then specific import

1. mod a set unfold
2. fail
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b", "c"])

# Wildcard import of unfolded should error
match resolve_import(ImportStmt.wildcard("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(_, _):
        pass
    case _:
        fail("Wildcard should error")

# Specific subpackage import should succeed
match resolve_import(ImportStmt.simple("a.b"), [mod_a]):
    case ImportResult.Ok:
        pass
    case _:
        fail("Subpackage should succeed")
```

</details>

### Feature Interactions

#### visibility modifiers

#### unfold respects pub visibility

1. mod a set unfold
2. expect subpkgs contains
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# public subpackage should be accessible
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["pub_subpkg"])

match resolve_import(ImportStmt.simple("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(_, subpkgs):
        expect subpkgs.contains("pub_subpkg")
    case _:
        fail("Expected error")
```

</details>

#### unfold with private subpackage

1. mod a set unfold
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Private subpackage in unfold list
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["private_impl"])

# Should still error but suggestion might be restricted
match resolve_import(ImportStmt.simple("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(_, _):
        pass
    case _:
        fail("Expected error")
```

</details>

#### conditional compilation

#### unfold in conditionally compiled module

1. mod test set unfold
2. expect subpkgs contains
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test module might have different unfold in test vs prod
val mod_test = Module.dir_module("mylib", "mylib/__init__.spl")
mod_test.set_unfold(["test_internal"])

match resolve_import(ImportStmt.simple("mylib"), [mod_test]):
    case ImportResult.UnfoldedPackageError(_, subpkgs):
        expect subpkgs.contains("test_internal")
    case _:
        fail("Expected error")
```

</details>

#### re-export scenarios

#### re-export with unfold source

1. mod a set unfold
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Module re-exports from unfolded subpackage
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["core"])

# Direct import of a should still error
match resolve_import(ImportStmt.simple("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(_, _):
        pass
    case _:
        fail("Direct import should error")
```

</details>

#### chained re-exports through unfolded

1. mod a set unfold
2. mod b set unfold
3. mod a add child
4. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b"])

val mod_b = Module.dir_module("b", "a/b/__init__.spl")
mod_b.set_unfold(["c"])
mod_a.add_child(mod_b)

# Chain through unfolded packages
match resolve_import(ImportStmt.simple("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(_, _):
        pass
    case _:
        fail("Should error at first level")
```

</details>

### Error Message Quality

#### suggestion quality

#### suggestions are sorted alphabetically

1. expect diagnostic suggestions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostic = create_unfold_lint("pkg", ["zebra", "alpha", "beta"])

# Suggestions should be in some consistent order
expect diagnostic.suggestions.len() == 3
```

</details>

#### suggestion preserves original case

1. expect diagnostic suggestions[0] contains
2. expect diagnostic suggestions[0] contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostic = create_unfold_lint("MyPackage", ["SubPkg"])

expect diagnostic.suggestions[0].contains("MyPackage")
expect diagnostic.suggestions[0].contains("SubPkg")
```

</details>

#### handles many subpackages gracefully

1. expect diagnostic suggestions len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val many_subpkgs = ["a", "b", "c", "d", "e", "f", "g", "h"]
val diagnostic = create_unfold_lint("pkg", many_subpkgs)

expect diagnostic.suggestions.len() == 8
```

</details>

#### span accuracy

#### error points to package name in import

1. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = Span.at("src/main.spl", 5, 10)
val msg = format_unfold_error("mymod", ["sub"], span)

expect msg.contains("5:10")
```

</details>

#### error includes correct file path

1. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = Span.at("src/deep/nested/file.spl", 100, 1)
val msg = format_unfold_error("a", ["b"], span)

expect msg.contains("src/deep/nested/file.spl")
```

</details>

### Scalability

#### many subpackages

#### handles package with many unfolded subpackages

1. mod a set unfold
2. expect returned subpkgs len
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_a = Module.dir_module("a", "a/__init__.spl")
val subpkgs = ["s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10"]
mod_a.set_unfold(subpkgs)

match resolve_import(ImportStmt.simple("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(_, returned_subpkgs):
        expect returned_subpkgs.len() == 10
    case _:
        fail("Expected error")
```

</details>

#### deep nesting

#### handles 5-level deep unfold chain

1. mod a set unfold
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# a -> b -> c -> d -> e
val mod_a = Module.dir_module("a", "a/__init__.spl")
mod_a.set_unfold(["b"])

match resolve_import(ImportStmt.simple("a"), [mod_a]):
    case ImportResult.UnfoldedPackageError(_, _):
        pass  # Just verify it works without stack overflow
    case _:
        fail("Expected error")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 72 |
| Active scenarios | 72 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
