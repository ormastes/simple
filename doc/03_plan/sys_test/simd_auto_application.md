# System Test Plan: SIMD Auto-Application

Date: 2026-05-03

## Compiler surface

- verify elementwise add/sub/mul/xor recipes are recognized
- verify unsupported shapes remain scalar
- verify FP reductions still require `fast_math`
- verify matrix-kernel inner loops are recognized conservatively

## Backend capability surface

- verify idiom-to-feature-class classification
- verify preferred lane-count helpers per target family
- verify unsupported idioms remain ungenerated or scalar-fallback eligible

## Library parity follow-up

- crypto scalar vs SIMD parity
- compression scalar vs SIMD parity
- forced scalar vs forced vector policy checks once target-plumbing lands
