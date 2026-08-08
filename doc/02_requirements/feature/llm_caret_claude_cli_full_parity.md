# LLM Caret Claude CLI Full Parity - Feature Requirements

Date: 2026-07-05

- REQ-LLM-CARET-FULL-001: Every file under
  `tmp/claude/claude-code-main/src` must be represented in the full-parity file
  matrix with a concrete Simple target under `src/app/llm_caret/claude_full/`.
- REQ-LLM-CARET-FULL-002: Every extracted Claude class, function,
  function-like exported const, type, and interface must be represented in the
  symbol matrix with a planned Simple symbol and a parity test gate.
- REQ-LLM-CARET-FULL-003: Every feature group generated from the Claude source
  tree must have a target MDSOC+ capsule and phase.
- REQ-LLM-CARET-FULL-004: The implementation cannot be called complete while
  any file, feature, class, function, type, or interface row remains unimplemented
  or untested.
- REQ-LLM-CARET-FULL-005: Each mapped Simple target file must meet or exceed
  the mapped Claude source file LOC unless a later approved architecture change
  replaces this strict size gate with stronger generated behavioral evidence.
- REQ-LLM-CARET-FULL-006: No feature is out of scope for the full-parity lane;
  phased implementation is allowed, skipped completion is not.
- REQ-LLM-CARET-FULL-007: Progress and completion reports must include the
  count and percentage of original Claude `*.ts`/`*.tsx` files whose mapped
  Simple target is at least 80% of the original file LOC. The 2026-07-07
  baseline is 551/1884 files at or above 80%, with 1333/1884 not yet at that
  threshold.
