<!-- codex-research -->
# Optimization Plugin JIT Hotspot Domain Research

Date: 2026-05-24

## Findings

Modern optimizing runtimes separate compile-time optimization from runtime profile-driven optimization:

- A compiler pass pipeline can optimize ahead of time from static facts.
- A JIT uses profile facts such as hot counts, stable types, branch behavior, and guards to decide when a region is worth compiling or specializing.
- A correct JIT keeps a fallback path and deoptimizes or invalidates specialized code when runtime guards no longer hold.

## Implications For Simple

Simple Optimization Plugin should not be limited to compiler optimization. The same provider metadata should also describe runtime hotspot optimizers:

- Provider kind: `jit-hotspot`.
- Lookup kind: usually `pipeline-pass`, because hotspot planning is region/function scoped rather than per-symbol exact lookup.
- Required facts: runtime profile and guard facts.
- Produced facts: a hotspot plan, not an unconditional semantic rewrite.
- Safety: runtime-guarded; disabling the provider must preserve interpreter/native fallback behavior.

## Near-Term Constraint

The current repo has JIT integration docs and execution-manager references, but the safe first implementation is the provider contract and tests. Backend-specific hotspot compilation should be added after the contract is stable and after representative profile/invalidation tests exist.
