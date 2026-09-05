<!-- codex-research -->
# Rust Runtime Minimization - Feature Requirement Options

Date: 2026-05-04

## Option A - Default C-Core OS Primitives, Pure Simple Policy

Description: Make file I/O, env/cwd/time, stdin/stdout, terminal raw mode, and basic TCP/UDP sockets available through a stable C-core ABI. Implement path handling, protocol framing, HTTP basics, MCP/LSP JSON helpers, and TUI widgets in Simple. Rust-hosted lanes remain opt-in.

Pros:

- Directly matches the executable-size objective.
- Aligns with `default_native_runtime_shift_to_c_core_abi`.
- Keeps Rust only where selected.
- Smallest realistic blast radius for file/network/TUI.

Cons:

- Requires careful cross-platform C shims.
- Process execution and advanced async may remain hosted-only until later.
- Needs ABI conformance tests on Linux, BSD, macOS, and Windows.

Effort: L, about 20-35 files across runtime C, compiler ABI lists, stdlib wrappers, and tests.

## Option B - Aggressive Pure Simple Runtime First

Description: Port as much runtime behavior as possible into Simple immediately, using C only for unavoidable syscalls and handles. Push process management, protocol stacks, CLI, TUI, and async coordination into Simple in the first phase.

Pros:

- Maximizes Rust removal.
- Accelerates self-hosting pressure and dogfooding.
- Makes hosted Rust dependencies more visible.

Cons:

- Larger schedule and higher risk.
- May increase binary size if Simple runtime support code is not optimized yet.
- Could block on missing language/codegen features.

Effort: XL, about 50-90 files across runtime, stdlib families, apps, and compiler support.

## Option C - MCP/LSP-Only Rust Removal First

Description: Scope the first migration to MCP/LSP startup and read-only workspace tools. Add only the C-core ABI needed for framed stdio, JSON protocol, env/cwd/time, and file read/existence. Defer general network and TUI.

Pros:

- Closest to existing inventory and tests.
- Faster measurable win for packaged tool binaries.
- Lower risk than a general runtime migration.

Cons:

- Does not fully satisfy the user’s network/fileio/TUI ambition.
- Could create duplicated APIs if the general runtime split follows later.
- Process-backed tools still need hosted-only gates.

Effort: M, about 12-20 files.

## Option D - Keep Rust Runtime, Size-Optimize Packaging

Description: Keep the current Rust runtime assumptions but improve stripping, link-time optimization, feature flags, and packaging closure selection.

Pros:

- Lowest implementation risk.
- Preserves existing Rust integrations.
- Can reduce some package sizes quickly.

Cons:

- Conflicts with the stated goal to move away from Rust base dependencies.
- Does not make network/fileio/TUI possible without Rust.
- Leaves default generated executables dependent on Rust closure decisions.

Effort: M, about 10-20 files.

## Recommended Selection

Choose Option A. It satisfies the objective without pretending that unsafe ABI and OS integration can be pure Simple today.

