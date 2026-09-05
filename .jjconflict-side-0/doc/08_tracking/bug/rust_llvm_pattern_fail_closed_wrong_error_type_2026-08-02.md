# Rust LLVM pattern fail-closed branch returns the wrong error type

- **Status:** FIXED
- **Owner:** `codex-stage4-bootstrap-close`
- **Found:** 2026-08-02 during unlimited incremental bootstrap
- **Area:** Rust bootstrap boundary, LLVM MIR lowering

## Exact reproduction

`--full-bootstrap` failed while compiling `simple-compiler` with E0308 at
`codegen/llvm/functions.rs`: the unsupported-pattern fail-closed branch returned
`Err(String)` from a function whose error type is `CompileError`.

## Pure-Simple-first check

The pure-Simple owner already rejects unsupported enum arm patterns in
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`; it does not
contain the Rust typing defect. The boundary twin must preserve that fail-closed
policy using `CompileError::Codegen`.

## Regression family

The exact regression constructs an unsupported tuple `PatternTest` and requires
a typed codegen error. The adjacent control constructs a supported literal
pattern and requires successful LLVM lowering, preventing a broad rejection.
