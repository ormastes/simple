# Executable Size Reduction - Feature Options

Codex options, 2026-04-23.

## Option A - Release Guardrails Only

Add package/release size checks and require stripped packaged binaries.

Pros: smallest code change; catches future release regressions. Cons: does not reduce generated native executable size by itself. Effort: low.

## Option B - Native Linker Runtime Retention

Replace ELF runtime `--whole-archive` with precise runtime symbol roots derived from object undefineds plus known runtime lifecycle and dispatch roots.

Pros: directly targets generated native executable bloat; keeps compatibility fallback through an environment variable. Cons: requires careful symbol-root tests. Effort: medium.

## Option C - Combined Selected Scope

Do Option A and Option B, and pass `--strip` for packaged native MCP/LSP binaries.

Pros: fixes the measured native-linker bloat, strips release package binaries, and adds regression budgets. Cons: dependency-closure reductions remain future work. Effort: medium.

Selected: Option C, based on the user-provided implementation plan.
