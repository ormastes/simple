# Errors

Status: production API contract.

Simple diagnostics must be precise enough for CLI users, LSP clients, MCP tools,
and tests to consume the same error without bespoke parsing.

## Diagnostic Shape

Every compiler, tool, and public library diagnostic should expose:

| Field | Contract |
| --- | --- |
| `code` | Stable machine-readable code. Compiler errors use `E####`; warnings use `W####`. |
| `severity` | `error`, `warning`, `info`, or `hint`. |
| `message` | One sentence naming the problem in user terms. |
| `path` | Source path when known. |
| `line` / `column` | 1-based primary location when known. |
| `span` | Optional start/end range for editors. |
| `hint` | Actionable next step, not a restatement. |
| `related` | Optional secondary locations with labels. |
| `fixes` | Optional structured edits for safe automatic repair. |

## Message Style

- Say what is wrong first: `Unknown method 'push' for String`.
- Include the expected and actual values when available.
- Prefer concrete hints: `Use 'append' for StringBuilder` rather than
  `Check the receiver type`.
- Do not expose internal phase names in primary messages.
- Do not suggest changes that may alter semantics unless the fix is explicit and
  opt-in.
- Warnings must state whether compilation continues and what future gate may
  promote the warning to an error.

## Error Categories

| Range | Category |
| --- | --- |
| `E0000-E0999` | Syntax, parser recovery, malformed literals |
| `E1000-E1999` | Name resolution, type checking, calls, fields, imports |
| `E2000-E2999` | Runtime contracts, casts, FFI, platform boundaries |
| `E3000-E3999` | Module, package, target, and build configuration |
| `E4000-E4999` | Tooling protocols: LSP, DAP, MCP, formatter, docs |
| `W0000-W0999` | Style, deprecation, compatibility, migration warnings |
| `W1000-W1999` | Production boundary warnings: GC/no-GC, noalloc, target family |

## Result Contract

Public fallible APIs return `Result<T, E>`. Use `Option<T>` only when absence is
ordinary and does not carry useful failure detail.

Required patterns:

- `parse_*` returns `Result<T, ParseError>`.
- `get` returns `Option<T>` for optional lookup.
- `fetch` returns `Result<T, LookupError>` or accepts a default.
- `open`, `read`, `write`, `connect`, `compile`, and `decode` return `Result`.
- `must_*` may abort or panic only in test helpers, assertions, or process-level
  entrypoints where the docs state the behavior.

## Warning Policy

Warnings are production work items, not noise. A warning must have one of:

- a documented compatibility reason,
- a tracked migration path,
- or a target/preset condition that explains why it is not an error yet.

New warning classes must include a regression test proving the warning text,
code, and source span. If a warning guards a production boundary, the test must
also cover whether the relevant target preset keeps it a warning or promotes it
to an error.
