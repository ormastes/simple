# Domain Research: SIMD / Matrix / Bit-ISA Auto-Application

Date: 2026-05-03
Owner: Codex

## Phase-1 takeaways

- Compiler-first rollout is the correct boundary: recognize portable scalar idioms in MIR, then lower to target-specific instructions where available.
- Bitmanip idioms should stay scalar in portable MIR and only become ISA-specific late:
  - rotate
  - popcount
  - clz / ctz
  - bswap
  - bitreverse
  - carryless multiply
  - CRC32
- Matrix support should start from kernel recognition, not arbitrary source-level matrix expressions:
  - dot product
  - outer-product update
  - matvec
  - blocked micro-kernel
- `fast_math` is appropriate for FP reductions and reassociation, not for exact elementwise vector rewrites.

## Implications for Simple

- Target capability routing needs both fine-grained idioms and coarse planning classes.
- A reusable lane-selection helper is needed so the optimizer can ask for preferred width without baking in AVX2 assumptions.
- Crypto and compression stay the first adoption tier because they already contain:
  - xor-heavy loops
  - checksum/clmul idioms
  - reduction-like inner kernels

## Deferred domain work

- dedicated AMX/SME/tile-engine backend support
- generalized matrix-expression lowering
- profitability tuning from measured startup/latency/RSS evidence rather than static cost hints alone
