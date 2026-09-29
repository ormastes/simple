# LLM Caret Claude CLI Harden - System Test Plan

Date: 2026-07-05

## Gate

`test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl`

## Assertions

- trace report exists;
- checker exists;
- report contains MDSOC+ boundary, source mapping, function trace, and Claude
  source trace sections;
- checker computes source-file and source-LOC mapping coverage and reports PASS
  at >=80%;
- checker confirms every current Simple `fn`, `struct`, and `extern fn` symbol
  has a trace entry.
