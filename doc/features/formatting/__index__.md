# Formatting & Lints (#1131-#1145)

Deterministic code formatting and semantic lint rules.

## Features

### Canonical Formatter (#1131-#1133)

| ID | Feature | Difficulty | Status | Impl |
|----|---------|------------|--------|------|
| #1131 | Formatter implementation | 3 | ✅ | S |
| #1132 | Idempotent formatting | 2 | ✅ | S |
| #1133 | Format-on-save IDE integration | 2 | 📋 | R |

### Semantic Lints (#1134-#1138)

| ID | Feature | Difficulty | Status | Impl |
|----|---------|------------|--------|------|
| #1134 | Lint rule implementation | 3 | ✅ | S |
| #1135 | Built-in lint rules | 3 | ✅ | S |
| #1136 | Configurable severity | 2 | ✅ | S |
| #1137 | `simple lint` command | 2 | ✅ | S |
| #1138 | Lint output formatting | 2 | ✅ | S |

### Lint Control (#1139-#1145)

| ID | Feature | Difficulty | Status | Impl |
|----|---------|------------|--------|------|
| #1139 | `#[allow]`/`#[deny]`/`#[warn]` attributes | 2 | ✅ | R |
| #1140-#1141 | CLI level control | 2 | ✅ | R |
| #1142 | Auto-fix CLI (`simple fix`) | 4 | 📋 | R |
| #1143 | Fix-it hints | 2 | ✅ | R |
| #1144 | Lint configuration in simple.sdn | 2 | ✅ | R |
| #1145 | `--explain` for error codes | 2 | ✅ | R |

## Summary

**Status:** 13/15 Complete (87%)

## Lint Categories (14 rules)

| Category | Rules | Description |
|----------|-------|-------------|
| Safety | S001-S003 | Unused Result, null deref, unsafe |
| Correctness | C001-C003 | Unreachable code, non-exhaustive match, type mismatch |
| Warning | W001-W003 | Unused variable/import, dead code |
| Style | ST001-ST003 | Naming conventions (Allow by default) |
| Concurrency | CC001-CC002 | Shared mutable state, thread safety |

## Implementation

- **Formatter:** `simple/app/formatter/main.spl` (166 lines)
- **Linter:** `simple/app/lint/main.spl` (262 lines)
- **Rust lint system:** `src/compiler/src/lint/`

## Documentation

- [spec/formatting_lints.md](../../spec/formatting_lints.md)
- Archived in [feature_done_9.md](../done/feature_done_9.md)
