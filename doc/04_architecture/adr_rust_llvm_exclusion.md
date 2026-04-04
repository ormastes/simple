# ADR: rust-llvm Formal Exclusion from LLVM Family Claim

**Date:** 2026-04-04  
**Status:** Accepted  
**Decision:** rust-llvm is bootstrap-only and formally excluded from the public LLVM backend family claim

## Context

The Simple compiler has three LLVM integration paths:

| Path | Binary | Purpose |
|------|--------|---------|
| `llvm-lib` | `bin/release/simple` | In-process libLLVM C API — production |
| `llvm` (CLI) | `bin/release/simple` | External llc/opt/clang — production |
| `rust-llvm` | `src/compiler_rust/` | Rust seed bootstrap — development only |

The LLVM full-family completion program requires every public backend row to be resolved to `stable` or `unsupported`. The question is whether `rust-llvm` should be included in this matrix.

## Decision

**rust-llvm is formally excluded from the public LLVM backend family.**

It is a bootstrap-only path used during the staged bootstrap process:
1. Rust seed compiles the Simple compiler (using Rust's LLVM)
2. The resulting Simple binary recompiles itself (using Simple's own LLVM backends)
3. The final self-hosted binary has no Rust dependency

rust-llvm serves a different purpose (seed compilation) than the production backends (user code compilation). Including it in the family claim would require maintaining proof parity for a path that end users never interact with.

## Consequences

- The public LLVM support matrix (`llvm_support_matrix.spl`) contains only `llvm-lib` and `llvm` columns
- No proof requirements exist for rust-llvm in the family completion program
- rust-llvm continues to function for bootstrap but is not counted in support claims
- README and audit documents describe only the two public backend paths
- If rust-llvm is ever promoted to a production backend, a new ADR must be written

## Alternatives Considered

1. **Promote rust-llvm to public backend** — Rejected: would require per-target proof parity for a path only used in development
2. **Remove rust-llvm entirely** — Rejected: still needed for bootstrap from scratch
3. **Rename to avoid confusion** — Not needed: the exclusion ADR is sufficient documentation
