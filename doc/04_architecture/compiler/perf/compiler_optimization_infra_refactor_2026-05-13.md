# Compiler Optimization Infrastructure Refactor

Date: 2026-05-13

## Decision

Simple optimization infrastructure uses a common rule-provider interface for
pattern rules. Hot, stable, release-critical rules are built into the compiler
binary. Dynamic providers are represented in the interface but not inserted into
hot lookup paths until the optimizer ABI and manifest format are versioned.

## Rationale

The MIR pattern pass runs in a function/block/instruction walk. Per-call-site
allocation or table rebuilding directly taxes compile time. Built-in rule
providers allow direct lookup and stable release behavior. Dynamic loading is
still valuable for rare or experimental optimizer modules, but it should be a
late-bound extension surface, not the default compiler hot path.

## Current Boundary

- `rule_engine.spl` owns common provider metadata and lookup statistics.
- `rules_crypto.spl` owns built-in cipher rule definitions and direct callee
  lookup.
- `pattern_dispatch.spl` owns MIR rewrite traversal and target/cost gating.
- LLVM backend optimization remains separate and should continue to prefer
  LLVM default `O*` pass pipelines.

## Follow-Up

The next structural refactor should introduce a reusable MIR visitor/transform
API so instruction-rewrite passes do not each reimplement module/function/block
walking.
