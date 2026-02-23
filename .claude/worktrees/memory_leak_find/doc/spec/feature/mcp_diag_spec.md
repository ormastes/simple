# MCP Virtual Diagnostic Tools

**Feature ID:** #MCP-002 | **Category:** Application | **Status:** Active

_Source: `test/feature/app/mcp_diag_spec.spl`_

---

## Overview

Tests the MCP virtual diagnostic tool suite including the core diagnostic engine, read-only tools,
edit/delta tools, and VCS tools. Covers severity tag formatting, diagnostic output parsing from
compiler error formats, virtual text overlay with inline error/warning annotations and easyfix
hints, delta computation between baseline and current diagnostics (resolved/introduced/remaining),
JSON serialization of diagnostic entries and results, and schema generation for all tool categories.

## Syntax

```simple
val entries = parse_diag_output("error[E:type_mismatch]: line 5:3: expected i64, got text", 1, "test.spl")
expect(entries[0].severity).to_equal("error")

val delta = compute_delta(baseline, current)
expect(delta.resolved.len()).to_equal(1)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 35 |

## Test Structure

### MCP Virtual Diagnostic Tools

#### diag_core - severity_tag

- ✅ returns [E] for error
- ✅ returns [W] for warning
- ✅ returns [I] for info
- ✅ returns [H] for hint
- ✅ returns [?] for unknown
#### diag_core - pad_line

- ✅ pads short line to target column
- ✅ does not truncate long lines
#### diag_core - parse_diag_output

- ✅ returns empty for exit code 0
- ✅ parses error bracket format
- ✅ parses error semantic format
- ✅ parses warning format
- ✅ parses multiple diagnostics
#### diag_core - overlay_virtual_text

- ✅ shows clean lines without annotation
- ✅ annotates line with error entry
- ✅ shows easyfix hint when show_hints is true
- ✅ hides easyfix when show_hints is false
#### diag_core - compute_delta

- ✅ detects resolved diagnostics
- ✅ detects introduced diagnostics
- ✅ detects remaining diagnostics
- ✅ handles mixed delta
#### diag_core - format_delta_text

- ✅ formats delta summary
#### diag_core - JSON serialization

- ✅ serializes DiagEntry to JSON
- ✅ serializes DiagEntry without easyfix
- ✅ serializes DiagResult to JSON
#### tool schemas - read tools

- ✅ generates simple_read schema
- ✅ generates simple_check schema
- ✅ generates simple_symbols schema
- ✅ generates simple_status schema
#### tool schemas - edit tools

- ✅ generates simple_edit schema
- ✅ generates simple_multi_edit schema
- ✅ generates simple_run schema
#### tool schemas - vcs tools

- ✅ generates simple_diff schema
- ✅ generates simple_log schema
- ✅ generates simple_squash schema
- ✅ generates simple_new schema

