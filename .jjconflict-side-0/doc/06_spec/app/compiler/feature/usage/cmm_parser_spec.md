# CMM Parser Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CMM-PARSE |
| Category | Tooling |
| Status | Implemented |
| Source | `test/feature/usage/cmm_lsp/cmm_parser_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 82 |
| Active scenarios | 82 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/cmm_lsp/cmm_parser/result.json` |

## Scenarios

- parses empty source
- parses single comment line
- parses double-slash comment
- parses multiple comment lines
- parses blank lines
- parses simple label
- parses label with underscore
- parses label with alphanumeric name
- parses label followed by commands
- parses simple identifier command
- parses dot command
- parses multi-level dot command
- parses command with hex parameter
- parses command with option parameter
- parses command with string parameter
- parses device-qualified command
- parses simple IF with inline body
- parses IF with block body
- parses IF with ELSE
- parses IF with comparison condition
- parses IF with hex comparison
- parses WHILE with function condition
- parses WHILE with macro condition
- parses WHILE with block body
- parses simple GOTO
- parses GOSUB without arguments
- parses GOSUB with arguments
- parses GOSUB with multiple arguments
- parses RETURN without value
- parses RETURN with value
- parses DO with filename
- parses DO with arguments
- parses ENDDO without return value
- parses ENDDO with return values
- parses RUN with filename
- parses END
- parses STOP
- parses CONTINUE
- parses JUMPTO
- parses LOCAL with single macro
- parses LOCAL with multiple macros
- parses GLOBAL declaration
- parses PRIVATE declaration
- parses ENTRY with parameters
- parses ENTRY with single parameter
- parses macro assign with integer
- parses macro assign with hex value
- parses macro assign with string
- parses macro assign with expression
- parses macro assign with function call
- parses empty macro assignment
- parses recursive macro assign
- parses empty block
- parses block with single statement
- parses block with multiple statements
- parses nested blocks
- parses PRINT with string
- parses PRINT with multiple expressions
- parses OPEN with channel and mode
- parses CLOSE
- parses WRITE to channel
- parses READ from channel
- parses APPEND
- parses WAIT with time literal
- parses WAIT with second time literal
- parses ON ERROR GOTO
- parses ON ERROR CONTinue
- parses ON STOP GOSUB
- parses REPEAT with count
- parses REPEAT with block body
- parses flash setup subroutine
- parses CPU setup script
- parses script with macro loop
- parses script with conditional and subroutine
- parses script with DO call
- parses script with file I/O
- parses script with multiple labels and gotos
- parses data dump and load commands
- reports no errors for valid source
- file_path defaults to empty
- parses comments interleaved with commands
- parses blank lines between statements
