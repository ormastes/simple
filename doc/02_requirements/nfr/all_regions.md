<!-- codex-research -->
# All Regions NFR Requirements

Filed: 2026-04-22

- NFR-001: Parser changes must remain backward-compatible and contextual; existing identifiers should not become hard reserved words unless explicitly justified.
- NFR-002: Initial raw-block parsing must preserve payload text, nesting, and source spans for diagnostics and tooling.
- NFR-003: Domain blocks must not add hot-path full-tree scans, repeated file rereads, shell-outs, or retry sleeps.
- NFR-004: Tooling-visible domain blocks must appear in Tree-sitter/outline/LSP surfaces before semantic exporters are considered complete.
- NFR-005: Every domain exporter/importer must include round-trip or conformance tests tied to its named external standard.
- NFR-006: For MCP/LSP-visible parser changes, startup path, cache/index strategy, invalidation, representative request latency, and RSS must be reviewed before release.

