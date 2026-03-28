# Dependency Graphs

This repository maintains two dependency graphs: the Rust workspace crate graph and
the Simple package/module graph. Both are cycle-free by construction or validation.

## Rust Workspace (Cargo)

Rust crate dependencies are defined in `Cargo.toml` at the workspace root and in
each crate directory under `src/`. Cargo forbids cyclic crate dependencies, so
the workspace graph is acyclic by design.

To inspect the graph, use `cargo metadata` and filter to workspace members.
This is the source of truth for crate-level dependencies.

### Current Workspace Graph

Derived from `cargo metadata` on this workspace (workspace-member edges only):

```
arch_test: simple-dependency-tracker
simple-common: -
simple-compiler: simple-common, simple-dependency-tracker, simple-loader, simple-native-loader, simple-parser, simple-runtime, simple-sdn, simple-type
simple-dap: simple-common, simple-compiler, simple-parser
simple-db: simple-common
simple-dependency-tracker: simple-common, simple-parser
simple-driver: simple-common, simple-compiler, simple-dependency-tracker, simple-loader, simple-log, simple-native-loader, simple-parser, simple-pkg, simple-runtime, simple-term-io
simple-embedded: -
simple-gpu: simple-common
simple-loader: simple-common
simple-log: -
simple-lsp: simple-common, simple-compiler, simple-parser
simple-native-loader: simple-common, simple-runtime
simple-parser: simple-common
simple-pkg: -
simple-runtime: simple-common
simple-sdn: -
simple-simd: simple-common
simple-sqp: simple-common, simple-db
simple-stub: simple-loader
simple-term-io: simple-native-loader
simple-tests: simple-common, simple-compiler, simple-dependency-tracker, simple-driver, simple-loader, simple-parser, simple-pkg, simple-runtime, simple-type, simple_mock_helper
simple-type: simple-parser
simple-ui: simple-parser, simple-runtime
simple-wasm-runtime: simple-common, simple-runtime
simple_mock_helper: -
```

## Simple Package Graph (simple.toml)

The Simple package manager builds a dependency graph from `simple.toml` manifests
in `src/pkg/src/resolver/graph.rs`. The resolver adds packages as it walks path
dependencies and records edges by package name.

Cycle prevention happens during insertion:

- `DependencyGraph::add` rejects edges that would introduce a cycle.
- The error is reported as `PkgError::CircularDependency` with a path like
  `a -> b -> c -> a`.
- `topological_order` remains available for install ordering and validation.

## Simple Module Import Graph

The compiler tracks module imports with `ImportGraph` in
`src/dependency_tracker/src/graph.rs`.

- Regular imports (`use`, `common use`, `export use`) participate in cycle checks.
- Type-only imports (`use type`) are tracked but excluded from runtime cycle detection.
- The module resolver calls `check_cycles` and fails compilation on cycles.

## Child Module Visibility Rules

The visibility system enforces that child modules cannot export beyond their parent's
control. This is implemented in `src/dependency_tracker/src/visibility.rs`.

**Key Rules:**

1. A child module's exports are **blocked by default** unless the parent explicitly allows.
2. For a symbol to be externally visible, ALL conditions must be met:
   - Symbol is declared `pub` in the child module
   - Parent's `__init__.spl` has `pub mod child`
   - Parent's `__init__.spl` has `export use child.symbol` (or `export use child.*`)
3. `export use child.*` only exports non-macro items; macros require `auto import`.

**Proven Properties (Lean theorems):**

- `private_stays_private`: A private symbol cannot become public
- `private_module_restricts`: A symbol in a private module cannot become public
- `must_be_exported`: A symbol must be explicitly exported to be visible externally

## Dependency Graph Generator Tool

The `simple_depgraph` tool generates `.__init__.spl` files (dot-prefixed) containing
dependency analysis for Simple modules. It's implemented in Simple language with AOP logging.

**Location:** `simple/app/depgraph/`

### Usage

```bash
# Analyze single directory
simple_depgraph ./src/mymodule/

# Recursive analysis with verbose logging
simple_depgraph ./src/ --recursive --verbose

# Dry run (print analysis without writing files)
simple_depgraph ./src/api --dry-run --summary
```

### Options

| Option | Description |
|--------|-------------|
| `--recursive` | Analyze subdirectories recursively |
| `--verbose` | Enable verbose AOP logging |
| `--no-comments` | Omit comments from generated files |
| `--summary` | Print summary report after generation |
| `--dry-run` | Print analysis without writing files |
| `--help` | Show usage information |

### Output Format

The tool generates `.__init__.spl` (dot-prefixed, auto-generated) files:

```simple
# Auto-generated dependency analysis
# DO NOT EDIT - regenerate with: simple_depgraph ./src/mymodule

# External dependencies (imports from outside this module tree)
# external: std.io
# external: core.json

# Child modules
pub mod api       # externally visible
pub mod types     # externally visible
mod internal      # private (no pub mod)
mod utils         # BLOCKED: no export use

# Re-exports (accessible to parent)
export use api.Handler
export use types.Config

# Visibility Summary
# ------------------
# Externally visible: api, types
# Blocked (need export use): internal, utils
```

### AOP Logging

The tool uses AOP (Aspect-Oriented Programming) to log all operations:

```simple
# AOP advice declarations in main.spl
on pc{ execution(* scanner.scan_directory(..)) } use log_scan_before before
on pc{ execution(* analyzer.analyze_directory(..)) } use log_analyze_before before
on pc{ execution(* generator.write_dot_init(..)) } use log_generate_before before
```

When `--verbose` is enabled, logs include:
- `[SCAN]` - Directory scanning operations
- `[PARSE]` - File parsing operations
- `[ANALYZE]` - Dependency analysis operations
- `[GEN]` - File generation operations
- `[INFO]`, `[WARN]`, `[ERROR]` - Status messages

### Module Structure

```
simple/app/depgraph/
├── main.spl       # Entry point with AOP logging
├── scanner.spl    # Directory/file scanning
├── parser.spl     # Import extraction from .spl files
├── analyzer.spl   # Dependency analysis and visibility checking
└── generator.spl  # .__init__.spl file generation
```

### Tests

Specification tests in `simple/std_lib/test/unit/tooling/depgraph_spec.spl` define
the expected behavior using BDD-style sspec syntax.
