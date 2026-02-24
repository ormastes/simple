# MCP Protocol Compliance Spec

**Feature ID:** #MCP-PROTOCOL-001  
**Category:** Application / MCP  
**Status:** Active (Gap Tracking + Closure Plan)

_Source: `test/feature/app/mcp_protocol_gap_matrix_spec.spl`_

## Overview

Defines an explicit, test-backed matrix of:

1. Current MCP feature surface in active `simple-mcp`
2. Known command-level protocol gaps
3. Known response-format gaps
4. Planned phase breakdown for gap closure

This spec is a contract for documentation and planning completeness while implementation work proceeds.

## Feature Matrix Scope

### Current Tool Surface

- Debug tools: 16
- Debug-log tools: 6
- Diagnostic tools: 12
- Total advertised MCP tools: 34

### Known Command Gaps

- `resources/templates/list`
- `resources/read`
- `prompts/get`
- `completion/complete`
- `completions/complete`
- `logging/setLevel`
- `roots/list`

### Known Response-Format Gaps

- JSON-RPC `id` type preservation
- Capability declaration completeness
- Detailed tool schemas (`properties`/`required`)
- Tool-level error semantics (`isError` style)
- Structured tool payloads beyond JSON-in-text

## Acceptance Contract

The SSpec matrix must enforce:

1. Tool inventory counts and representative names
2. Full known-gap list presence
3. Gap-closure phase presence (`Phase 1` through `Phase 4`)
4. Cross-links to plan/research/design artifacts

## Runtime Verification

- `test/feature/app/mcp_protocol_runtime_spec.spl` validates wire-level support for:
  - `resources/templates/list`
  - `resources/read`
  - `prompts/get`
  - `completion/complete`
  - `logging/setLevel`
  - `roots/list`
  - initialize response id preservation
