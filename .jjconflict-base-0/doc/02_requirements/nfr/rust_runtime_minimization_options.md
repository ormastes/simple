<!-- codex-research -->
# Rust Runtime Minimization - NFR Options

Date: 2026-05-04

## Option 1 - Size-First Core Lane

Description: Core-generated hello/file/TUI/network smoke binaries must not link Rust runtime archives unless an explicit Rust-required feature is selected.

Targets:

- Core hello binary remains within the existing executable-size budget.
- File I/O smoke binary size is no more than 15% above hello on the same target.
- TUI smoke binary size is no more than 30% above hello before optional image/font/audio dependencies.
- Rust symbols are absent from core-lane binaries unless a test explicitly enables a Rust-hosted feature.

Pros:

- Direct, testable fit to the user objective.
- Prevents silent Rust dependency regressions.

Cons:

- Requires symbol and size audit tooling to be reliable across platforms.
- Some targets may need per-platform budgets.

Effort: M.

## Option 2 - Portability-First Core Lane

Description: Prioritize Linux, FreeBSD, macOS, and Windows behavior parity for C-core file/network/TUI shims before enforcing strict size targets.

Targets:

- ABI smoke tests pass on Linux and FreeBSD first.
- macOS and Windows shims compile behind platform gates.
- Size budgets are warnings until all four platforms have smoke coverage.

Pros:

- Reduces cross-platform correctness risk.
- Better fit if BSD/Windows support is the immediate priority.

Cons:

- Size regressions can slip during early migration.
- Slower feedback on the main executable-size goal.

Effort: L.

## Option 3 - Tooling-First Latency/RSS Gates

Description: Focus NFRs on MCP/LSP startup latency, request latency, RSS, and package closure size rather than generic runtime binary size.

Targets:

- MCP/LSP core-lane startup responds to initialize/tools-list without Rust-hosted runtime.
- Warm startup, representative request latency, and max RSS are recorded on realistic fixtures.
- Process-backed tools are explicitly reported as hosted-only until ported.

Pros:

- Aligns with existing MCP/LSP hot-path rules.
- Produces immediately useful tool-server evidence.

Cons:

- Does not fully cover general app file/network/TUI size.
- More specialized than the user’s broader runtime objective.

Effort: M.

## Recommended Selection

Choose Option 1, with Option 2’s platform smoke tests added as verification gates for any platform touched by the implementation.

