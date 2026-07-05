# LLM Caret Claude CLI Harden - Detail Design

Date: 2026-07-05

## Trace Report

`doc/09_report/llm_caret_claude_cli_traceability.md` contains:

- extracted Claude CLI feature groups;
- source file mapping table with LOC;
- Simple function/class trace;
- key Claude source trace.

## Checker

`scripts/check/check-llm-caret-claude-cli-trace.shs` scans
`src/app/llm_caret/*.spl`, counts files and LOC with mapping rows in the
report, and fails below 80%. It also extracts every current `fn`, `struct`, and
`extern fn` symbol and fails unless the report contains a backticked
`kind:name` token for each symbol.

## SSpec

`test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl` runs the
checker through `std.io_runtime.process_run` and checks the public PASS output.
