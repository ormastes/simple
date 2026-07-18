# Agent Task Plan: SIMD Auto-Application

Date: 2026-05-03

## Compiler infrastructure

- extend recipe metadata and legality scaffolding
- route vector width through shared capability helpers
- keep `fast_math` restricted to reduction-sensitive transforms

## Backend lowering

- x86: add portable bitmanip intrinsic lowering
- AArch64: add portable bitmanip intrinsic lowering
- RISC-V: add portable bitmanip intrinsic lowering

## Library adoption

- crypto: xor/rotate/clmul candidates
- compression: crc32/checksum/xor/match-copy candidates

## Matrix follow-up

- add dot-product rewrite
- add outer-product update rewrite
- add matvec profitability checks

## Verification

- capability helper unit specs
- auto-vectorize matcher specs
- backend lowering specs for new bit idioms
