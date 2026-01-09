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
