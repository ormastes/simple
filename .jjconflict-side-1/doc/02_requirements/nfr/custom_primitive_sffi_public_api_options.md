# Custom Primitive SFFI and Public API NFR Options

Date: 2026-04-20

## Option 1: Focused Regression Coverage

Require unit and integration tests for custom primitive SFFI fields, function signatures, bitfields, and primitive API lint output.

Pros:

- Fast feedback.
- Covers the requested behavior directly.

Cons:

- May miss backend ABI drift in less common targets.

Effort: Medium.

## Option 2: ABI and Layout Evidence

Option 1 plus generated C/LLVM signature checks, transparent layout checks, bitfield packing checks, and a public API audit report with reason codes.

Pros:

- Proves that custom primitives remain ABI-transparent.
- Makes public API migration reviewable.
- Catches pointer-vs-value lowering regressions.

Cons:

- More tests and fixtures to maintain.

Effort: Large.

## Option 3: Full Tooling Smoke Gate

Option 2 plus core runtime smoke, MCP native smoke, and representative compile/runtime checks because compiler and `src/lib` changes can affect language surface and tooling startup.

Pros:

- Strongest release confidence.
- Matches repo rules for compiler/core/lib changes.

Cons:

- Slowest verification path.
- May expose unrelated pre-existing failures.

Effort: Large.

## Recommendation

Use Option 3 for final verification, with Option 2 checks during development.
