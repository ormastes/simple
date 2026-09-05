# Decimal `u64` literals rejected through the signed range guard

## Status

Fixed in the Stage-4 LLVM 23.1 bootstrap lane on 2026-08-04.

## Symptom

The full CLI Stage-4 streaming parse rejected the valid FNV-1a offset basis
`14695981039346656037u64` in
`src/os/compositor/background_image_provider.spl` as out of range for `i64`.

## Root cause

The lexer preserved the `u64` suffix separately, but `parse_primary_expr`
decoded every decimal integer through `parser_guarded_int_text` before
constructing the suffixed AST node. The signed ceiling was therefore applied
before lowering could interpret the stored bits as unsigned.

## Fix and regression

Decimal literals carrying the exact `u64` suffix now use a guarded decoder
whose ceiling is `18446744073709551615`. The AST continues to store the wrapped
`i64` bit pattern, matching the established hex-literal and Rust-seed model.
Unsuffixed and other suffixed literals retain the existing signed ceiling.

The streaming module-surface lifecycle spec covers the FNV basis and u64 max
inside synthetic source text, exercising the exact Stage-4 parser path without
requiring the test harness itself to pre-parse those numeric tokens.
