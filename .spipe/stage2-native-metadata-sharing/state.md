# Stage 2 native metadata sharing

Status: implementation

## Problem

`compile_file_to_object` cloned project-wide structural maps and rebuilt the
global mangling suffix index for every compilation unit. A 615-module bootstrap
therefore repeated project-sized work hundreds of times on the native-build hot
path.

## Acceptance criteria

- AC-001: immutable project structural metadata is constructed once and shared
  with compilation units through `Arc`.
- AC-002: ambiguous field names retain the existing rule: ambiguous only when
  the same field occurs at different indexes.
- AC-003: the global mangling suffix index is built once per project.
- AC-004: insertion order does not change ambiguity results.
- AC-005: compiler library and focused regression tests compile and pass.

## Boundary decision

The pure-Simple native-build driver already delegates one project build through
the compiler boundary. The repeated work is inside the Rust seed's per-unit
project compiler, so the fix belongs at `ModuleImports`, the immutable
project-to-unit snapshot boundary.
