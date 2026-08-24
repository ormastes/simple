# MCP Bounded Text Assembly Specification

Source: `test/01_unit/app/mcp_unit/mcp_text_assembly_spec.spl`

## Contract

Both app and standard-library MCP JSON text escaping treat Unicode as opaque
UTF-8 text and escape only the historical backslash, quote, and line-feed set.
Tabs, carriage returns, NUL, backspace, form-feed, and other controls retain the
existing policy. Inputs without those three characters use the unchanged-value
fast path; other inputs use three ordered linear replacements.

Bounded first-line rendering retains the exact split, limit, truncation, and
trailing-newline behavior, including historical all-empty-line edge cases. It
records output fragments and joins once instead of copying a growing prefix.

## Executable scenarios

Paired executable specs cover empty, ASCII, mixed escaping, multibyte and astral
Unicode, raw controls, nonpositive limits, truncation, exact boundaries, and the
trailing-empty split behavior. They were added but not executed under the user's
no-verification instruction.
