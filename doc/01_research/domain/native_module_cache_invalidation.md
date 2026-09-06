<!-- codex-research -->
# Native module cache invalidation — domain research

## Rust

Rust persists a stable query dependency graph and 128-bit result fingerprints.
Its red-green algorithm reuses a node when dependencies remain green; even when
an input changes, recomputation can prove an unchanged semantic result and stop
propagation. Backend reuse is partitioned by codegen unit. Projection queries
act as change-propagation firewalls around broad compiler state.

Primary sources:

- https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation.html
- https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation-in-detail.html

## Swift

Swift records fine-grained provides/depends arcs for declarations and semantic
lookups, fingerprints graph nodes, integrates changed provisions during the
build, and rejects prior state on compiler/config mismatch. Removed provisions
and interrupted scheduled work remain dirty.

Primary sources:

- https://github.com/swiftlang/swift/blob/main/docs/DependencyAnalysis.md
- https://github.com/swiftlang/swift-driver/blob/main/Sources/SwiftDriver/IncrementalCompilation/ModuleDependencyGraphParts/Node.swift
- https://github.com/swiftlang/swift-driver/blob/main/Sources/SwiftDriver/IncrementalCompilation/IncrementalDependencyAndInputSetup.swift

## Bazel and Clang

Bazel keys isolated actions from declared inputs, tools, arguments, environment,
platform, and output names, while storing artifacts content-addressably. Clang
modules persist ASTs and retain references to their contributing headers so
cached modules can be validated against actual inputs.

Primary sources:

- https://bazel.build/remote/caching
- https://github.com/bazelbuild/bazel/blob/master/src/main/java/com/google/devtools/build/lib/remote/RemoteExecutionService.java
- https://clang.llvm.org/docs/Modules.html

## Application to Simple

Use stable semantic module identities and explicit dependency/resolution/layout
witnesses, not a global source hash. Separate action identity from output
content identity. Preserve fail-closed fallback and source-mutation admission
guards. Do not claim correctness from timestamps or selected import paths alone.
