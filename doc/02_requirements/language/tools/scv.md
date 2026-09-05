# SCV Feature Requirements

Status: selected requirements, 2026-05-14.

## Scope

`scv` is a new Simple-native versioning system. It should learn from Git and Jujutsu but own its object store, operation log, parser index, diff, merge, and gate model.

## Requirements

REQ-001: `scv` shall store exact file bytes as the primary repository truth for every private savepoint.

REQ-002: `scv` shall use content-addressed byte objects with stable IDs derived from raw bytes, not from parser output or file metadata alone.

REQ-003: `scv` shall model commits as immutable content snapshots and changes as stable logical units whose latest commit can be rewritten.

REQ-004: `scv` shall maintain an operation log that records repository views, operation parent pointers, workspace working-copy commits, bookmarks, and metadata.

REQ-005: `scv` shall support jj-like automatic private working-copy snapshots, including a watch command that can repeatedly create private savepoints as files change.

REQ-006: `scv` shall allow private savepoints even when parsing, compiling, or tests fail.

REQ-007: `scv` shall expose commit states at least for private, parse error, parsed ok, compile ok, test ok, and public ready.

REQ-008: `scv` shall provide fallback line-tree parsing for unsupported text files and chunk-tree parsing for binary files.

REQ-009: `scv` shall keep Tree-sitter parser data as a derived parser-aware index, never as the only source of repository truth.

REQ-010: `scv` shall support raw diff first, then syntax and formatting-policy diff views.

REQ-011: `scv` shall support file/tree merge first, then syntax-node fallback merge for same-shape text, then line fallback merge.

REQ-012: `scv` shall treat conflicts as repository data that can be saved and resolved later.

REQ-013: `scv` shall support parser registry and grammar lockfile metadata before auto-downloading parser code.

REQ-014: `scv` shall use Simple DB, hash, compression, atomic-write, and file I/O libraries where practical.

REQ-015: `scv` shall document x86-64 and ARM64 as primary developer targets, with x86, ARM32, RISC-V 64, and RISC-V 32 as compatibility targets where the Simple runtime supports them.

REQ-016: `scv` shall support private backup sync after verification gates pass, without treating that backup as shared/public publishing.

REQ-017: `scv` shall support a bounded public export artifact only after `public_ready`, without auto-pushing to a shared branch.

REQ-018: `scv` shall support explicit filesystem-backed public push only after `public_ready`, recording and verifying remote refs without publishing private or unverified commits.

## Deferred From First Slice

- Full Tree-sitter WASM grammar downloader. The current slice can install and lock local WASM grammar artifacts without executing them.
- GumTree-grade move/rename matching.
- Production pack GC and delta chains.
- Full Git import/export. The current slice provides a bounded Git fast-import export/import subset.
- Network/shared-branch publishing beyond filesystem remotes. The current slice can create gated public export artifacts and explicit filesystem-backed public pushes.
